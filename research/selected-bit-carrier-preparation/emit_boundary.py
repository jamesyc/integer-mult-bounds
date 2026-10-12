#!/usr/bin/env python3
"""Bounded exact literal projection. Does not import or execute the supplier.
Original #493 data: eumemic, with Anthropic Claude assistance, Apache-2.0.
This decoder/domain preparation: OpenAI assistance. No operator claim.
"""
from pathlib import Path
import datetime,gzip,hashlib,io,json,resource,time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
INPUT=ROOT/'research/e8-bit-carrier-skeleton/data/bit/bitE8mut-r489.json.gz'
COMPRESSED='835eb96e147740fc7454f8cfb3dbd34ae89524b1dbd89a61e9288eae8ab6a5b9'
DECODED='88435b75b8d6e5c722eb2aa1449f3a5e8e9601a9ffe243839ce1ec932ab76547'
MAX=1024*1024
H=lambda b:hashlib.sha256(b).hexdigest()

def strict_json(b):
 assert len(b)<=MAX
 def pairs(xs):
  d={}
  for k,v in xs:
   assert k not in d,'duplicate JSON key'
   d[k]=v
  return d
 def constant(x):raise ValueError('nonfinite JSON')
 return json.loads(b.decode('utf8'),object_pairs_hook=pairs,parse_constant=constant)

def integer(x):
 assert type(x)is int,'integer literal required'
 return str(x)

def nat(x):
 assert type(x)is int and x>=0,'natural literal required'
 return str(x)

def array(x,entry):
 assert type(x)is list,'list required'
 return '['+', '.join(entry(y)for y in x)+']'

def project(w):
 assert set(w)=={'A','B','C','D','R','coords','final','form','format','frames','h','lines','ret','scatter','start','v'}
 assert w['format']=='bitE8/1+mut'and w['form']=='<x,y>/2'
 assert [w['h'],w['v'],w['R']]==[8,120,489]
 fields=[('h','Nat',nat(w['h'])),('v','Nat',nat(w['v'])),('R','Nat',nat(w['R'])),
         ('format','String',json.dumps(w['format'])),('form','String',json.dumps(w['form'])),
         ('lines','List (List Int)',array(w['lines'],lambda x:array(x,integer))),
         ('frames','List (List Nat)',array(w['frames'],lambda x:array(x,nat))),
         ('start','List Nat',array(w['start'],nat)),('final','List Nat',array(w['final'],nat)),
         ('ret','List Nat',array(w['ret'],nat))]
 header='''/- Exact selected #493 raw boundary projection. Supplier: eumemic, with substantial
Anthropic Claude assistance; Apache-2.0, original package NOTICE/LICENSE retained.
Prepared with OpenAI assistance. Only the ten named raw fields are emitted.
No gate, operator, rank, price or global-schedule correctness is asserted here. -/
import Init
namespace CurrentMain.SelectedBitCarrierBoundary.Data
'''
 return header+'\n'.join('def '+name+' : '+ty+' := '+value+'\n'for name,ty,value in fields)+'''def registers : Nat := 2*v+R
end CurrentMain.SelectedBitCarrierBoundary.Data
'''

def main():
 resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2))
 resource.setrlimit(resource.RLIMIT_CPU,(15,15));t=time.monotonic()
 compressed=INPUT.read_bytes();assert len(compressed)==49154 and H(compressed)==COMPRESSED
 with gzip.GzipFile(fileobj=io.BytesIO(compressed))as z:decoded=z.read(MAX+1)
 assert len(decoded)==247056 and H(decoded)==DECODED
 w=strict_json(decoded);source=project(w).encode();assert len(source)<128*1024
 target=HERE/'SelectedBitCarrierBoundaryData.lean';assert not target.exists()
 with target.open('xb')as f:f.write(source)
 audit=dict(status='EXACT_LITERAL_PROJECTION_ONLY',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  input_path=str(INPUT.relative_to(ROOT)),compressed_sha256=COMPRESSED,decoded_sha256=DECODED,
  compressed_bytes=len(compressed),decoded_bytes=len(decoded),emitter_sha256=H(Path(__file__).read_bytes()),
  expected_raw_fields=sorted(w),projected_fields=['h','v','R','format','form','lines','frames','start','final','ret'],
  omitted_fields=['A','B','C','D','coords','scatter'],source_sha256=H(source),source_bytes=len(source),
  source_order_and_integer_literals_preserved=True,upstream_execution=False,compiler=False,
  elapsed_seconds=time.monotonic()-t,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,
  limits=dict(input_uncompressed_bytes=MAX,cpu_seconds=15,address_space_bytes=256*1024**2))
 with (HERE/'BOUNDARY_LITERAL_AUDIT.json').open('x')as f:json.dump(audit,f,indent=2);f.write('\n')
 print(json.dumps(audit,indent=2))

if __name__=='__main__':main()
