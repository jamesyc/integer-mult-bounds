#!/usr/bin/env python3
"""Exact two-field source projection, never executing the upstream supplier.
Supplier eumemic/Anthropic Claude, Apache-2.0. Prepared with OpenAI assistance.
"""
from pathlib import Path
import ast,datetime,gzip,hashlib,io,json,resource,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
INPUT=ROOT/'research/e8-bit-carrier-skeleton/data/bit/bitE8mut-r489.json.gz'
COMPRESSED='835eb96e147740fc7454f8cfb3dbd34ae89524b1dbd89a61e9288eae8ab6a5b9'
DECODED='88435b75b8d6e5c722eb2aa1449f3a5e8e9601a9ffe243839ce1ec932ab76547'
H=lambda b:hashlib.sha256(b).hexdigest()
def nat(x):
 assert type(x)is int and x>=0
 return str(x)
def array(x,f):
 assert type(x)is list
 return '['+', '.join(f(y)for y in x)+']'
def gate(x):
 assert type(x)is list and len(x)==3
 return '('+nat(x[0])+', '+nat(x[1])+', '+array(x[2],nat)+')'
def pairs(xs):
 d={}
 for k,v in xs:
  assert k not in d
  d[k]=v
 return d
def main():
 resource.setrlimit(resource.RLIMIT_AS,(268435456,268435456));resource.setrlimit(resource.RLIMIT_CPU,(15,15));t=time.monotonic()
 b=INPUT.read_bytes();assert len(b)==49154 and H(b)==COMPRESSED
 with gzip.GzipFile(fileobj=io.BytesIO(b))as z:raw=z.read(1048577)
 assert len(raw)==247056 and H(raw)==DECODED
 def bad(x):raise ValueError(x)
 w=json.loads(raw.decode(),object_pairs_hook=pairs,parse_constant=bad)
 assert set(w)=={'A','B','C','D','R','coords','final','form','format','frames','h','lines','ret','scatter','start','v'}
 assert [w['h'],w['v'],w['R']]==[8,120,489]
 gs=array(w['B'],gate);sc=array(w['scatter'],lambda x:array(x,nat))
 source='''/- Exact immutable PR493 B/scatter projection. Supplier eumemic, with
Anthropic Claude assistance; Apache-2.0, original NOTICE/LICENSE retained.
Prepared with OpenAI assistance. Frame, destination and ordered operands are
copied without deduplication or relabeling. Scatter remains a raw table. -/
import SelectedBitCarrierBoundaryCheck
namespace CurrentMain.SelectedBitCarrierPhaseB.Data
-- Triple order is exactly (frame ID, destination register, source registers).
def phaseB : List (Nat × Nat × List Nat) := '''+gs+'''
-- Row t names target120+t; entries are indices into the accepted ret list.
def scatter : List (List Nat) := '''+sc+'''
end CurrentMain.SelectedBitCarrierPhaseB.Data
'''
 # Independent syntax inversion of the generated literal payloads.
 reread_g=ast.literal_eval(source.split('def phaseB : List (Nat × Nat × List Nat) := ',1)[1].split('\n-- Row',1)[0]);reread_s=ast.literal_eval(source.split('def scatter : List (List Nat) := ',1)[1].split('\nend ',1)[0])
 assert [[a,b,c]for a,b,c in reread_g]==w['B'] and reread_s==w['scatter']
 out=HERE/'SelectedBitCarrierPhaseBData.lean'
 with out.open('x')as f:f.write(source)
 audit=dict(status='EXACT_TWO_FIELD_LITERAL_PROJECTION_AND_OWN_INVERSION_PASS',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),emitter_sha256=H(Path(__file__).read_bytes()),input_path=str(INPUT.relative_to(ROOT)),compressed_sha256=COMPRESSED,decoded_sha256=DECODED,decoded_bytes=len(raw),source_sha256=H(source.encode()),source_bytes=len(source.encode()),fields={'B':dict(rows=len(w['B']),operand_occurrences=sum(len(g[2])for g in w['B'])), 'scatter':dict(rows=len(w['scatter']),index_occurrences=sum(map(len,w['scatter'])))},order_and_multiplicity_preserved=True,original_supplier_executed=False,compiler=False,resources=dict(elapsed_seconds=time.monotonic()-t,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,decompressed_limit_bytes=1048577,cpu_seconds=15,address_space_bytes=268435456))
 with (HERE/'PHASE_B_LITERAL_AUDIT.json').open('x')as f:json.dump(audit,f,indent=2);f.write('\n')
 print(json.dumps(audit))
if __name__=='__main__':main()
