#define STRING_COUNT 0
/* Native support primitives. Protocol guards/actions are generated C below. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <limits.h>
#include <string.h>
#include <stdarg.h>
#include <errno.h>
#define LOG_CAP 131072
#define FIELD_CAP 64
#define SEQ_MOD INT64_C(4294967296)
typedef struct { char data[LOG_CAP]; size_t size; } Buffer;
const char *failure = NULL;
void text(Buffer *b, const char *s) {
    size_t n=strlen(s);
    if(n>=LOG_CAP-b->size) { failure="output_capacity"; return; }
    memcpy(b->data+b->size,s,n+1); b->size+=n;
}
void number(Buffer *b,int64_t n) { char s[32]; snprintf(s,sizeof(s),"%" PRId64,n); text(b,s); }
int64_t add(int64_t a,int64_t b) {
    if((b>0 && a>INT64_MAX-b)||(b<0 && a<INT64_MIN-b)) {failure="integer_overflow";return 0;}
    return a+b;
}
int64_t sub(int64_t a,int64_t b) {
    if((b>0 && a<INT64_MIN+b)||(b<0 && a>INT64_MAX+b)) {failure="integer_overflow";return 0;}
    return a-b;
}
int64_t mul(int64_t a,int64_t b) {
    if(a==0||b==0)return 0;
    if((a==-1&&b==INT64_MIN)||(b==-1&&a==INT64_MIN)) {failure="integer_overflow";return 0;}
    if((a>0 && b>0 && a>INT64_MAX/b)||(a>0 && b<0 && b<INT64_MIN/a)||
       (a<0 && b>0 && a<INT64_MIN/b)||(a<0 && b<0 && a<INT64_MAX/b)) {
        failure="integer_overflow";return 0;
    }
    return a*b;
}
int64_t seqadd(int64_t a,int64_t b) {
    int64_t n=(a+b%SEQ_MOD)%SEQ_MOD; return n<0?n+SEQ_MOD:n;
}
int64_t distance(int64_t a,int64_t b) { return (b-a+SEQ_MOD)%SEQ_MOD; }
int64_t minimum(int64_t a,int64_t b) { return a<b?a:b; }
int valid(int64_t n,int kind) {
    return kind==0 || (kind==1 && (n==0||n==1)) || (kind==2 && n>=0 && n<SEQ_MOD) || (kind==4 && n>=0 && n<STRING_COUNT);
}

void json_string(Buffer *out,const char *s) {
    const unsigned char *p=(const unsigned char *)s;char escaped[8];
    text(out,"\"");
    for(;*p;p++) {
        if(*p=='"'||*p=='\\'){escaped[0]='\\';escaped[1]=(char)*p;escaped[2]=0;text(out,escaped);}
        else if(*p<32){snprintf(escaped,sizeof(escaped),"\\u%04x",*p);text(out,escaped);}
        else {escaped[0]=(char)*p;escaped[1]=0;text(out,escaped);}
    }
    text(out,"\"");
}
/* Bytes are value types. Capacity is an explicit execution domain, never silent
   truncation. IR slice arguments are OFFSET and COUNT, clamped independently. */
#define BYTE_CAP 4096
#define INPUT_CAP (2*BYTE_CAP*FIELD_CAP+4096)
typedef struct { size_t len; unsigned char data[BYTE_CAP]; } Bytes;
Bytes byte_literal(const unsigned char *p,size_t n) {
    Bytes out={0};
    if(n>BYTE_CAP){failure="byte_capacity";return out;}
    out.len=n;if(n)memcpy(out.data,p,n);return out;
}
Bytes byte_concat(Bytes a,Bytes b) {
    Bytes out={0};
    if(a.len>BYTE_CAP||b.len>BYTE_CAP||b.len>BYTE_CAP-a.len){failure="byte_capacity";return out;}
    out.len=a.len+b.len;memcpy(out.data,a.data,a.len);memcpy(out.data+a.len,b.data,b.len);return out;
}
Bytes byte_slice(Bytes a,int64_t offset,int64_t count) {
    Bytes out={0};size_t start,n;
    if(a.len>BYTE_CAP){failure="byte_capacity";return out;}
    start=offset<0?0:(uint64_t)offset>a.len?a.len:(size_t)offset;
    n=count<0?0:(uint64_t)count>a.len-start?a.len-start:(size_t)count;
    out.len=n;if(n)memcpy(out.data,a.data+start,n);return out;
}
int byte_equal(Bytes a,Bytes b) {return a.len==b.len&&memcmp(a.data,b.data,a.len)==0;}
int64_t byte_at_or_zero(Bytes a,int64_t offset) {
    if(a.len>BYTE_CAP){failure="byte_capacity";return 0;}
    if(offset<0||(uint64_t)offset>=a.len)return 0;
    return a.data[(size_t)offset];
}
Bytes byte_pack8(int64_t n) {
    unsigned char b[1]={(uint8_t)n};return byte_literal(b,1);
}
Bytes byte_pack16be(int64_t n) {
    uint16_t v=(uint16_t)n;unsigned char b[2]={(unsigned char)(v>>8),(unsigned char)(v&255)};
    return byte_literal(b,2);
}
Bytes byte_pack32be(int64_t n) {
    uint32_t v=(uint32_t)n;unsigned char b[4]={(unsigned char)(v>>24),(unsigned char)(v>>16),(unsigned char)(v>>8),(unsigned char)(v&255)};
    return byte_literal(b,4);
}
int64_t byte_checksum16(Bytes a) {
    size_t i;uint32_t sum=0;
    if(a.len>BYTE_CAP){failure="byte_capacity";return 0;}
    for(i=0;i<a.len;i+=2){
        uint32_t word=((uint32_t)a.data[i]<<8)+(i+1<a.len?a.data[i+1]:0);
        sum+=word;sum=(sum&UINT32_C(65535))+(sum>>16);
    }
    return (int64_t)(UINT32_C(65535)-sum);
}
void byte_json(Buffer *out,Bytes a) {
    size_t i;text(out,"[");for(i=0;i<a.len;i++){if(i)text(out,",");number(out,a.data[i]);}text(out,"]");
}
int byte_nibble(char c) {
    if(c>='0'&&c<='9')return c-'0';
    if(c>='a'&&c<='f')return c-'a'+10;
    if(c>='A'&&c<='F')return c-'A'+10;
    return -1;
}
int parse_bytes(const char *s,Bytes *out) {
    size_t n,i;*out=(Bytes){0};
    if(!s||s[0]!='b'||s[1]!=':'){failure="invalid_bytes_token";return 0;}
    n=strlen(s+2);
    if(n%2){failure="invalid_bytes_token";return 0;}
    if(n/2>BYTE_CAP){failure="byte_capacity";return 0;}
    for(i=0;i<n/2;i++){
        int a=byte_nibble(s[2+2*i]),b=byte_nibble(s[3+2*i]);
        if(a<0||b<0){failure="invalid_bytes_token";return 0;}out->data[i]=(unsigned char)((a<<4)|b);
    }
    out->len=n/2;return 1;
}

enum { NV=1, NB=0, NT=0 };
typedef struct { int state; int64_t now,v[NV?NV:1],due[NT?NT:1]; Bytes b[NB?NB:1]; int active[NT?NT:1]; } Machine;
const char *state_names[]={"READY"};
const char *event_names[]={"inspect"};
const char *timer_names[]={""};
int event_origin[]={0};
int event_fields[]={3};
int event_kinds[1][FIELD_CAP]={{3,0,1}};
int timer_events[]={0};
int variable_kinds[]={0};
int variable_byte_index[]={-1};
const char *variable_names[]={"result"};
const char *source_json_strings[]={""};
const char *source_json(int64_t i) { if(i<0||i>=STRING_COUNT){failure="string_domain";return "\"\"";}return source_json_strings[i];}
void initialize(Machine *m) { memset(m,0,sizeof(*m)); m->state=0;
m->v[0]=INT64_C(0);
}
int invariants(Machine *m) { (void)m; if(failure)return 0;
if(!(((m->v[0]>=INT64_C(0))&&(m->v[0]<=INT64_C(255))))) {failure="invariant:range";return 0;}
return failure==NULL; }
void snapshot(Buffer *out,Machine *m) { int first=1;
text(out,"{\"state\":");
switch(m->state) {
case 0:
text(out,"\"READY\"");
break;
default:failure="invalid_state";}
text(out,",\"variables\":{");
text(out,"\"result\":");
number(out,m->v[0]);
text(out,"},\"timers\":{");
(void)first;
text(out,"}}");
}
static int rule_guard_0(Machine *m,int64_t *f,Bytes *bf) { (void)m; (void)f; (void)bf; return 1; }
static int rule_action_0(Machine *m,int64_t *f,Bytes *bf,Buffer *log) { Buffer messages={{0},0}; int emitted=0; (void)f; (void)bf; (void)emitted;
m->v[0]=(f[2]?byte_at_or_zero(bf[0],f[1]):INT64_C(0));
if(failure)return 0;
{
if(emitted++)text(&messages,",");
text(&messages,"{\"message\":\"observed\",\"fields\":{");
text(&messages,"\"value\":");
number(&messages,m->v[0]);
text(&messages,"}}");
}
if(failure)return 0;
m->state=0; if(!invariants(m))return 0;
text(log,"{\"status\":\"transition\",\"transition\":\"INSPECT\",\"requirements\":[\"BYTES\"],\"time_ms\":");
number(log,m->now);
text(log,",\"event\":{\"name\":\"inspect\",\"fields\":{");
text(log,"\"data\":");
byte_json(log,bf[0]);
text(log,",\"index\":");
number(log,f[1]);
text(log,",\"enabled\":");
text(log,f[2]?"true":"false");
text(log,"}},\"after\":");
snapshot(log,m);
text(log,",\"emitted\":[");
text(log,messages.data);
text(log,"]}\012");
return failure==NULL; }
int fire(Machine *m,int event,int64_t *f,Bytes *bf,int expiring,Buffer *log) { int match=-1,count=0;
if(m->state==0&&event==0&&rule_guard_0(m,f,bf)) {match=0;count++;}
if(failure)return 0;
if(count!=1){failure=count?"rule_conflict":"uncovered_event";return 0;} if(expiring>=0)m->active[expiring]=0; switch(match) {
case 0:return rule_action_0(m,f,bf,log);
default:failure="invalid_rule";return 0;} }
/* Line interface for independent execution; no JSON model is read at runtime.
   I variable-index integer (before B), B, D milliseconds event integer-fields,
   T milliseconds. Each operation is committed atomically after all checks. */
int advance(Machine *m,int64_t at,Buffer *log) {
    int steps=0;
    if(at<m->now){failure="nonmonotonic_time";return 0;}
    for(;;) {
        int next=-1,i;
        for(i=0;i<NT;i++)if(m->active[i] && (next<0||m->due[i]<m->due[next]||
             (m->due[i]==m->due[next]&&strcmp(timer_names[i],timer_names[next])<0)))next=i;
        if(next<0||m->due[next]>at)break;
        if(++steps>4096){failure="timer_step_capacity";return 0;}
        m->now=m->due[next];
        if(!fire(m,timer_events[next],NULL,NULL,next,log)){if(!failure)failure="internal_transition_failure";return 0;}
    }
    m->now=at;return 1;
}
int parse_integer(const char *s,int64_t *out) {
    char *end; long long n;
    if(!s||!*s)return 0;
    errno=0;n=strtoll(s,&end,10);
    if(errno||*end||n<INT64_MIN||n>INT64_MAX)return 0;
    *out=(int64_t)n;return 1;
}
#ifdef HAS_TEXT_EVENTS
int parse_text_field(TextPool *pool, const char *token, int64_t *out) {
    return parse_text(pool, token, out);
}
#endif
void reply(Machine *m,const char *status,const char *error) {
    Buffer out={{0},0};
    text(&out,"{\"status\":\"");text(&out,status);text(&out,"\"");
    if(error){text(&out,",\"failure\":");json_string(&out,error);}
    text(&out,",\"snapshot\":");snapshot(&out,m);text(&out,"}\n");fputs(out.data,stdout);
}
int snapshot_fits(Machine *m) {
    Buffer preview={{0},0};snapshot(&preview,m);
    if(preview.size>LOG_CAP-4096)failure="output_capacity";
    return failure==NULL;
}
int main(void) {
    Machine committed;char line[INPUT_CAP];int begun=0,errors=0;
    initialize(&committed);
    while(fgets(line,sizeof(line),stdin)) {
        char *tokens[FIELD_CAP+4];int count=0,overflow=0,i,event=-1;char *token;
        int64_t at=0,fields[FIELD_CAP]={0};Bytes byte_fields[FIELD_CAP]={{0}};Machine candidate=committed;Buffer log={{0},0};
        failure=NULL;
        if(!strchr(line,'\n')&&!feof(stdin)){failure="input_capacity";while((i=getchar())!='\n'&&i!=EOF){} }
        token=strtok(line," \t\r\n");
        while(token){if(count<(int)(sizeof(tokens)/sizeof(tokens[0])))tokens[count++]=token;else overflow=1;token=strtok(NULL," \t\r\n");}
        if(!count)continue;
        if(overflow)failure="input_capacity";
        if(!failure && !strcmp(tokens[0],"I")) {
            int64_t index,value;
            if(begun||count!=3||!parse_integer(tokens[1],&index)||index<0||index>=NV)failure="invalid_initial_override";
            else if(variable_kinds[index]==3)parse_bytes(tokens[2],&candidate.b[variable_byte_index[index]]);
#ifdef HAS_TEXT_EVENTS
            else if(variable_kinds[index]==4) {
                if(!parse_text_field(&candidate.texts, tokens[2], &value)&&!failure) failure="invalid_initial_override";
                else if(!failure) candidate.v[index]=value;
            }
#endif
            else if(!parse_integer(tokens[2],&value)||!valid(value,variable_kinds[index]))failure="invalid_initial_override";
            else candidate.v[index]=value;
            if(!failure&&snapshot_fits(&candidate)){committed=candidate;continue;}
        } else if(!failure && !strcmp(tokens[0],"B")) {
            if(begun||count!=1)failure="invalid_begin";
            else if(invariants(&candidate)){begun=1;reply(&committed,"ready",NULL);continue;}
        } else if(!failure && (!strcmp(tokens[0],"D")||!strcmp(tokens[0],"T")
#ifdef WIRE_PROFILE
                  ||!strcmp(tokens[0],"P")
#endif
                  )) {
            if(!begun||count<2||!parse_integer(tokens[1],&at))failure="invalid_command";
            if(!failure && !strcmp(tokens[0],"D")) {
                if(count<3)failure="invalid_command";
                else {
                    for(i=0;i<(int)(sizeof(event_names)/sizeof(event_names[0]));i++)if(!strcmp(tokens[2],event_names[i]))event=i;
                    if(event<0)failure="unknown_event";
                    else if(event_origin[event])failure="timer_injection";
                    else if(count!=3+event_fields[event])failure="event_field_mismatch";
                    else for(i=0;i<event_fields[event]&&!failure;i++) {
                        if(event_kinds[event][i]==3)parse_bytes(tokens[3+i],&byte_fields[i]);
#ifdef HAS_TEXT_EVENTS
                        else if(event_kinds[event][i]==4) {
                            if(!parse_text_field(&candidate.texts, tokens[3+i], &fields[i])&&!failure) failure="invalid_event_value";
                        }
#endif
                        else if(!parse_integer(tokens[3+i],&fields[i])||!valid(fields[i],event_kinds[event][i]))failure="invalid_event_value";
                    }
                }
            }
#ifdef WIRE_PROFILE
            else if(!failure && !strcmp(tokens[0],"P")) {
                if(count!=3)failure="invalid_wire_command";
                else if(wire_decode(tokens[2],fields))event=WIRE_EVENT;
            }
#endif
            else if(!failure && count!=2)failure="invalid_command";
            if(!failure && advance(&candidate,at,&log)) {
                if(event>=0){if(!fire(&candidate,event,fields,byte_fields,-1,&log)&&!failure)failure="internal_transition_failure";}
                else if(!invariants(&candidate)&&!failure)failure="internal_invariant_failure";
            }
            if(!failure&&snapshot_fits(&candidate)){committed=candidate;fputs(log.data,stdout);reply(&committed,"ok",NULL);continue;}
        } else if(!failure)failure="invalid_command";
        errors++;reply(&committed,"error",failure?failure:"internal_error");
    }
    if(ferror(stdin))return 2;
    if(!begun)return 2;
    return errors?1:0;
}

