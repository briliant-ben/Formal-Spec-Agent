"""Bounded DeepSeek JSON gateway: no shell/tool execution from model responses.

Credentials stay in the gateway; candidate/model prompts never receive them.
A locked write-ahead ledger prevents duplicate paid calls and automatic retries.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import time
import urllib.request
import urllib.error

ENDPOINT='https://api.deepseek.com/chat/completions'


def write(path,value):path.write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')


def credential(path):
    key=os.environ.get('DEEPSEEK_API_KEY')
    if not key:
        p=Path(path)
        if p.stat().st_mode&0o077:raise ValueError('Credential file must be private to its owner')
        key=p.read_text().strip()
    if not key:raise ValueError('Missing API credential')
    return key


def request(messages,out,credential_file,model='deepseek-flash',max_tokens=4096,max_calls=12,timeout=180,thinking='disabled',reasoning_effort=None):
    if not isinstance(messages,list)or not messages or any(set(m)!={'role','content'}or m['role']not in ('system','user','assistant')or type(m['content'])is not str for m in messages):raise ValueError('Explicit text messages required')
    if type(max_tokens)is not int or max_tokens<16 or (max_calls is not None and (type(max_calls)is not int or max_calls<1)):raise ValueError('Invalid request budget configuration')
    if thinking not in ('enabled','disabled')or reasoning_effort not in (None,'low','high','max')or(thinking=='disabled'and reasoning_effort is not None):raise ValueError('Invalid reasoning configuration')
    payload=dict(model=model,messages=messages,response_format={'type':'json_object'},max_tokens=max_tokens,stream=False,thinking={'type':thinking})
    if reasoning_effort is not None:payload['reasoning_effort']=reasoning_effort
    body=json.dumps(payload,ensure_ascii=False).encode()
    if len(body)>96000:raise ValueError('Prompt byte budget exceeded')
    digest=hashlib.sha256(body).hexdigest();out=Path(out);out.mkdir(parents=True,exist_ok=True);out.chmod(0o700)
    ledger_file=out/'ledger.json';lock=out/'ledger.lock'
    def update(fn):
        with lock.open('a')as f:
            fcntl.flock(f,fcntl.LOCK_EX);ledger=json.loads(ledger_file.read_text())if ledger_file.exists()else{}
            result=fn(ledger);write(ledger_file,ledger);return result
    def admit(ledger):
        if digest in ledger:return ledger[digest]
        if max_calls is not None and len(ledger)>=max_calls:raise ValueError('Paid request count budget exhausted')
        row=dict(status='pending',request_sha256=digest,model=model,max_tokens=max_tokens,thinking=thinking,reasoning_effort=reasoning_effort,prompt_bytes=len(body),started_at=time.time(),usage=None)
        ledger[digest]=row;return None
    prior=update(admit)
    if prior is not None:
        if prior['status']=='completed':return dict(**prior,cached=True)
        raise ValueError('Previous identical request failed or is uncertain; no automatic paid retry')
    record=dict(status='uncertain',provider_response_received=False,request_sha256=digest,model=model,max_tokens=max_tokens,thinking=thinking,reasoning_effort=reasoning_effort,prompt_bytes=len(body),usage=None)
    try:
        key=credential(credential_file)
        req=urllib.request.Request(ENDPOINT,data=body,headers={'Content-Type':'application/json','Authorization':'Bearer '+key})
        opener=urllib.request.build_opener(urllib.request.ProxyHandler({}))
        with opener.open(req,timeout=timeout)as response:raw=response.read(2*1024*1024+1)
        if len(raw)>2*1024*1024:raise ValueError('Provider response byte budget exceeded')
        if key.encode()in raw:raise ValueError('Credential appeared in provider output; response not retained')
        answer=json.loads(raw);record['usage']=answer.get('usage')
        record['status']='invalid_response';record['provider_response_received']=True
        provider_path=out/(digest+'.provider.json');provider_path.write_bytes(raw)
        record['provider_response_file']=provider_path.name
        choice=answer['choices'][0]
        if choice['finish_reason']!='stop':raise ValueError('Provider result incomplete')
        text=choice['message'].get('content','')
        if not text.strip():raise ValueError('Provider returned blank JSON content')
        parsed=json.loads(text)
        if not isinstance(parsed,dict):raise ValueError('Provider JSON object required')
        path=out/(digest+'.json');write(path,dict(request_sha256=digest,model=answer.get('model'),response=parsed,usage=record['usage'],provider_id=answer.get('id')))
        record.update(status='completed',response_file=path.name,finished_at=time.time())
    except urllib.error.HTTPError as error:
        # Never log headers, raw HTTP bodies or provider exception strings.
        record.update(status='failed',http_status=error.code,error='provider_http_error',finished_at=time.time())
    except Exception as error:
        record.update(error=type(error).__name__,finished_at=time.time())
    update(lambda ledger:ledger.__setitem__(digest,record))
    if record['status']!='completed':raise ValueError('Provider request did not complete; see sanitized ledger, no automatic retry')
    return dict(**record,cached=False)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--messages',required=True);p.add_argument('--out',required=True);p.add_argument('--credential-file',required=True);p.add_argument('--model',default='deepseek-flash');p.add_argument('--max-tokens',type=int,default=4096);p.add_argument('--max-calls',type=int,default=12);a=p.parse_args()
    try:r=request(json.loads(Path(a.messages).read_text()),a.out,a.credential_file,a.model,a.max_tokens,a.max_calls)
    except (ValueError,OSError)as error:r=dict(status='rejected',reason=str(error));print(json.dumps(r));raise SystemExit(1)
    print(json.dumps(r))
