#!/usr/bin/env python3
"""Bounded, advisory-only delimiter scan for this selected-source generator.

This is not a Lean lexer, parser, type checker or admission gate. It recognizes
ASCII (),[],{} plus Lean tuple ⟨⟩; nested /- -/ and -- comments, ordinary strings, a documented character-literal
subset, identifier primes, and «quoted identifiers». Backtick quotations,
interpolated/raw strings, unsupported character forms and depth/size limits
and other Unicode bracket notation produce INCONCLUSIVE. A balanced result says nothing about valid Lean syntax.
All outcomes exit zero; consumers must retain science/API/compiler review.
"""
import argparse,bisect,hashlib,json,re,time
from pathlib import Path
MAX_BYTES=1024*1024
MAX_DEPTH=4096
RAW=re.compile(r'r#+"')
CHAR=re.compile(r"'(?:[^'\\\n\r]|\\(?:[\\'\"abfnrtv0]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|u\{[0-9a-fA-F]+\}))'")

def scan(text):
    stack=[];issues=[];count=0;i=0;n=len(text)
    breaks=[-1]+[j for j,c in enumerate(text) if c=='\n']
    def loc(j):
        line=bisect.bisect_left(breaks,j)
        return {'offset':j,'line':line,'column':j-breaks[line-1]}
    def result(status,reason=None):
        return {'status':status,'reason':reason,'advisory_only':True,
                'parser_or_kernel_claim':False,'delimiter_subset':'ASCII (), [], {} plus Lean tuple ⟨⟩',
                'issue_count':count,'issues':issues[:32],'issue_output_limit':32}
    def issue(kind,j,**extra):
        nonlocal count
        count+=1
        if len(issues)<32:issues.append({'kind':kind,**loc(j),**extra})
    while i<n:
        if text.startswith('--',i):
            end=text.find('\n',i+2);i=n if end<0 else end+1;continue
        if text.startswith('/-',i):
            depth=1;i+=2
            while i<n and depth:
                if text.startswith('/-',i):depth+=1;i+=2
                elif text.startswith('-/',i):depth-=1;i+=2
                else:i+=1
                if depth>MAX_DEPTH:return result('INCONCLUSIVE','comment nesting bound')
            if depth:return result('INCONCLUSIVE','unterminated block comment')
            continue
        c=text[i]
        if c=='`':return result('INCONCLUSIVE','backtick quotation outside supported subset')
        if c=='r' and RAW.match(text,i):
            return result('INCONCLUSIVE','raw string outside supported subset')
        if c=='«':
            end=text.find('»',i+1)
            if end<0 or '«' in text[i+1:end]:return result('INCONCLUSIVE','unterminated or nested quoted identifier')
            i=end+1;continue
        if c=='"':
            if i and text[i-1]=='!':return result('INCONCLUSIVE','interpolated string outside supported subset')
            if i and text[i-1]=='r' and (i==1 or not(text[i-2].isalnum()or text[i-2]=='_')):
                return result('INCONCLUSIVE','raw string outside supported subset')
            i+=1
            while i<n and text[i]!='"':
                if text[i]=='\\':i+=2
                else:i+=1
            if i>=n:return result('INCONCLUSIVE','unterminated ordinary string')
            i+=1;continue
        if c=="'":
            if i and (text[i-1].isalnum()or text[i-1] in "_'!?"):
                i+=1;continue
            m=CHAR.match(text,i)
            if not m:return result('INCONCLUSIVE','character/quotation form outside supported subset')
            i=m.end();continue
        if c in '‹›⟦⟧⦃⦄⟪⟫':return result('INCONCLUSIVE','Unicode bracket notation outside supported subset')
        if c in '([{⟨':
            stack.append((c,i))
            if len(stack)>MAX_DEPTH:return result('INCONCLUSIVE','delimiter nesting bound')
        elif c in ')]}⟩':
            if not stack:issue('unmatched_close',i,token=c)
            elif stack[-1][0] != {')':'(',']':'[','}':'{','⟩':'⟨'}[c]:
                issue('mismatched_close',i,token=c,opening=stack[-1][0]);stack.pop()
            else:stack.pop()
        i+=1
    for c,j in stack:issue('unclosed_open',j,token=c)
    return result('ADVISORY_DELIMITER_ISSUES' if count else 'ADVISORY_NO_ASCII_IMBALANCE')

def check_file(path):
    start=time.perf_counter()
    try:
        with Path(path).open('rb') as f:data=f.read(MAX_BYTES+1)
        if len(data)>MAX_BYTES:out={'status':'INCONCLUSIVE','reason':'source byte bound','advisory_only':True,'parser_or_kernel_claim':False}
        else:
            try:out=scan(data.decode('utf-8'))
            except UnicodeDecodeError:out={'status':'INCONCLUSIVE','reason':'not UTF-8','advisory_only':True,'parser_or_kernel_claim':False}
        out.update(bytes_read=len(data),source_sha256=hashlib.sha256(data).hexdigest() if len(data)<=MAX_BYTES else None)
    except OSError as e:out={'status':'INCONCLUSIVE','reason':'file read failed: '+type(e).__name__,'advisory_only':True,'parser_or_kernel_claim':False}
    out.update(path=str(path),elapsed_seconds=time.perf_counter()-start,max_source_bytes=MAX_BYTES)
    return out

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source');a=p.parse_args()
    print(json.dumps(check_file(a.source),indent=2))
