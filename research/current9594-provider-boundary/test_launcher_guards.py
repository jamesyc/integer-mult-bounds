"""Bounded synthetic guards; no upstream source import or execution."""
from pathlib import Path
import ast, datetime, gzip, hashlib, importlib.util, json, tempfile, time
HERE=Path(__file__).resolve().parent
source=HERE/'run_ck_generation.py';ast.parse(source.read_text())
spec=importlib.util.spec_from_file_location('owned_launcher',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
checks=[]
def rejected(name,fn):
 try:fn()
 except (ValueError,FileNotFoundError):checks.append({'name':name,'status':'REJECTED_AS_REQUIRED'})
 else:raise AssertionError(name)
start=time.monotonic()
plan,guard=m.guard(True)
with tempfile.TemporaryDirectory(prefix='ck-control-fixture-',dir='/tmp')as d:
 root=Path(d);p=root/'recipe.json';p.write_bytes(b'{"input":1}\n');h=m.sha(p);m.exact(p,h)
 p.write_bytes(b'{"input":2}\n');rejected('mutated source bytes',lambda:m.exact(p,h))
 rejected('missing source',lambda:m.exact(root/'absent',h))
 g=root/'output.json.gz';g.write_bytes(gzip.compress(b'{"value":1}',mtime=0));expected=hashlib.sha256(b'{"value":1}').hexdigest();m.compare_content(g,expected)
 rejected('mutated expected content digest',lambda:m.compare_content(g,'0'*64))
 alias=root/'alias.json';alias.symlink_to(p);rejected('symlink source',lambda:m.exact(alias,m.sha(p)))
 p.write_bytes(b'{"x":1,"x":2}');rejected('duplicate JSON key',lambda:m.read(p))
 # Standard-library-only process-group termination smoke; actual output remains absent.
 m.OUT=root/'synthetic';m.OUT.mkdir();m.EVID=root/'evidence';m.EVID.mkdir();(m.EVID/'home').mkdir()
 argv=[str(m.PYTHON),'-I','-B','-c','import os,time; p=os.fork(); time.sleep(20)']
 result=m.run_child(argv,root/'group.log',time.monotonic()+5,job_review_seconds=.15)
 assert result['stop_reason']=='REVIEW_JOB_WALL' and result['exit_code']<0
 assert not [r for r in m.group_sample(result['pid'])if r['state']!='Z']
 checks.append({'name':'synthetic process-group review stop and cleanup','status':'PASS','process':result})
out={'status':'PASS_DRY_GUARD_AND_SYNTHETIC_NEGATIVES','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':time.monotonic()-start,'driver_sha256':m.sha(source),'plan_sha256':m.sha(HERE/'CK_GENERATION_RESOURCE_PROPOSAL.json'),'dry_guard':guard,'checks':checks,'supplier_processes_executed':0,'generation_output_absent':not Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction/bank/current9594_ck_generation/output').exists(),'limits':'Synthetic process validates kill/cleanup only; no observed supplier time/memory or full semantic artifact acceptance.'}
p=HERE/'LAUNCHER_DRY_NEGATIVE_RESULT.json';p.write_text(json.dumps(out,indent=2)+'\n');print(p,m.sha(p));print('driver',m.sha(source),'elapsed',out['seconds'])
