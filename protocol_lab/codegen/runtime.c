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
