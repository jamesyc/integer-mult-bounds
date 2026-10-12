"""Bounded synthetic guards; no upstream source import or execution."""
from pathlib import Path
import ast, datetime, fcntl, gzip, hashlib, importlib.util, json, os, signal, subprocess, tempfile, time
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
 for owner_signal in [signal.SIGTERM,signal.SIGHUP]:
  area=root/('signal-'+str(owner_signal));area.mkdir();(area/'output').mkdir();(area/'home').mkdir()
  owner_code="""import importlib.util,pathlib,sys,fcntl
p=pathlib.Path(sys.argv[1]);root=pathlib.Path(sys.argv[2]);sp=importlib.util.spec_from_file_location('launcher',p);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.EVID=root;m.OUT=root/'output';m.install_owner_signal_handlers()
with (root/'lock').open('a+')as f:
 fcntl.flock(f,fcntl.LOCK_EX)
 try:m.run_child([str(m.PYTHON),'-I','-B','-u','-c','import os,time; print(os.getpid(),flush=True); os.fork(); time.sleep(20)'],root/'child.log',m.time.monotonic()+10)
 finally:
  (root/'cleanup_finished').write_text('after_run_child_finally')
  fcntl.flock(f,fcntl.LOCK_UN)
"""
  owner=subprocess.Popen([str(m.PYTHON),'-I','-B','-c',owner_code,str(source),str(area)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  child_pid=None
  try:
   deadline=time.monotonic()+3
   while time.monotonic()<deadline:
    f=area/'child.log'
    if f.exists()and f.read_text().strip():child_pid=int(f.read_text().strip().splitlines()[0]);break
    if owner.poll()is not None:raise AssertionError('smoke owner exited early')
    time.sleep(.01)
   assert child_pid is not None
   os.kill(owner.pid,owner_signal);stdout,stderr=owner.communicate(timeout=3)
   assert owner.returncode==128+owner_signal,(owner.returncode,stderr)
   assert (area/'cleanup_finished').read_text()=='after_run_child_finally'
   assert not [r for r in m.group_sample(child_pid)if r['state']!='Z']
   with (area/'lock').open('r')as f:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
   checks.append({'name':'owner '+signal.Signals(owner_signal).name+' cleanup before lock release','status':'PASS','owner_exit':owner.returncode,'child_group':child_pid,'stderr_bytes':len(stderr)})
  finally:
   if owner.poll()is None:owner.kill();owner.wait()
   if child_pid is not None:
    try:os.killpg(child_pid,signal.SIGKILL)
    except ProcessLookupError:pass

out={'status':'PASS_DRY_GUARD_AND_SYNTHETIC_NEGATIVES','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':time.monotonic()-start,'driver_sha256':m.sha(source),'plan_sha256':m.sha(HERE/'CK_GENERATION_RESOURCE_PROPOSAL.json'),'dry_guard':guard,'checks':checks,'supplier_processes_executed':0,'generation_output_absent':not Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction/bank/current9594_ck_generation/output').exists(),'limits':'Synthetic process validates kill/cleanup only; no observed supplier time/memory or full semantic artifact acceptance.'}
p=HERE/'LAUNCHER_DRY_NEGATIVE_RESULT.json';p.write_text(json.dumps(out,indent=2)+'\n');print(p,m.sha(p));print('driver',m.sha(source),'elapsed',out['seconds'])
