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
