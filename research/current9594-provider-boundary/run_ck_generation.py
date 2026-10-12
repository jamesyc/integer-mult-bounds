#!/usr/bin/env python3
"""Fixed six-command ck materialization. Default is a read-only dry guard.
No supplier imports occur in this driver. Execute requires an exact reviewed
admission document; every intrinsic child check runs in the unchanged source.
"""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, importlib.util, json, math, os
import resource, signal, subprocess, time, gzip
HERE=Path(__file__).resolve().parent
ROOT=Path('/workspace/shared/integer-mult-git/checks/main-9594b61-readback')
EVID=Path('/workspace/scratch/c569c316cd54/recovery_20261011/post114_reconstruction/bank/current9594_ck_generation')
OUT=EVID/'output'
PYTHON=Path('/usr/bin/python3.13')
SLOT=Path('/workspace/scratch/c569c316cd54/integer_mult_research/research/current_main_lean_team_20261009/tools/lean_check.py')
PINS={HERE/'CK_GENERATION_RESOURCE_PROPOSAL.json':'716be0008796486f47844ce287bff05eecdb49ea8cd040669b7406bb4f568ba6',HERE/'CK_GENERATION_INPUTS.json':'ec45dff85be3991f39ec4fbdefc88d968392c727c99519e6555ee596814e652c',SLOT:'b71431bd34bfae67677ad6e8b49207c23ee2ba936c8507202416db4e0af22207',PYTHON:'889c603f0d17cb54060951bcf4c4f9b8c9ebd9e52b392c70209bbb9755d797d9'}
PINS[Path('/etc/python3.13/sitecustomize.py')]='43d81125d92376b1a69d53a71126a041cc9a18d8080e92dea0a2ae23be138b1e'
HEAD='9594b61042164a27a31e44d8c3197f231470eda0'
MAX_JSON=32*1024*1024
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb')as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def reject_constant(x):raise ValueError('non-finite JSON: '+x)
def unique(pairs):
 out={}
 for k,v in pairs:
  if k in out:raise ValueError('duplicate JSON key: '+k)
  out[k]=v
 return out
def read(path):
 p=Path(path)
 with (gzip.open(p,'rb')if p.suffix=='.gz'else p.open('rb'))as f:b=f.read(MAX_JSON+1)
 if len(b)>MAX_JSON:raise ValueError('JSON exceeds 32 MiB')
 return json.loads(b,object_pairs_hook=unique,parse_constant=reject_constant)
def payload_sha(path):
 h=hashlib.sha256();total=0
 with gzip.open(path,'rb')as f:
  for b in iter(lambda:f.read(1024*1024),b''):
   total+=len(b)
   if total>MAX_JSON:raise ValueError('gzip payload exceeds 32 MiB')
   h.update(b)
 return h.hexdigest()
def json_sha(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()
def exact(path,value):
 p=Path(path)
 if not p.is_file() or p.is_symlink() or p.resolve()!=p:raise ValueError('missing/nonregular/symlink file: '+str(p))
 if sha(p)!=value:raise ValueError('source hash mismatch: '+str(p))
def save(name,value):
 p=EVID/name;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('x',encoding='utf-8')as f:f.write(json.dumps(value,indent=2,allow_nan=False)+'\n')
def env(home):return {'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC','HOME':str(home)}
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),*args],text=True)
def records():
 inv=read(HERE/'CK_GENERATION_INPUTS.json')
 return inv,[*inv['files'],*inv['root_source_pins'],*inv['source_attribution'],inv['selected_manifest']]
def guard(require_absent):
 startup=Path('/usr/lib/python3.13/sitecustomize.py')
 if not startup.is_symlink() or os.readlink(startup)!='/etc/python3.13/sitecustomize.py' or startup.resolve()!=Path('/etc/python3.13/sitecustomize.py'):raise ValueError('system startup symlink changed')
 for p,h in PINS.items():exact(p,h)
 plan=read(HERE/'CK_GENERATION_RESOURCE_PROPOSAL.json');inv,rows=records()
 if git('rev-parse','HEAD').strip()!=HEAD:raise ValueError('readback HEAD changed')
 if git('status','--porcelain=v1','--untracked-files=all'):raise ValueError('readback worktree dirty')
 if require_absent and (OUT.exists() or OUT.is_symlink()):raise ValueError('output already exists')
 if subprocess.check_output([str(PYTHON),'--version'],text=True).strip()!='Python 3.13.5':raise ValueError('interpreter version')
 for row in rows:
  p=ROOT/row['path'];exact(p,row['sha256'])
  if p.stat().st_size!=row['bytes']:raise ValueError('size: '+str(p))
 assert plan['head']==inv['head']==HEAD and len(plan['steps'])==6
 sources={str(ROOT/r['path']) for r in inv['files']}
 for step in plan['steps']:
  a=step['argv'];assert a[:7]==[str(PYTHON),'-I','-B','-X','utf8','-X','int_max_str_digits=0']
  assert a[7] in sources and a[8] in sources
  for p in step['outputs']:assert Path(p).is_relative_to(OUT)
 # PathFinder resolves selected custom imports without importing them.
 custom=[ROOT/r['path'] for r in rows if Path(r['path']).name in ('gk_word.py','gk_common.py','clifford_exact.py')]
 probe="""import importlib.machinery,importlib.util,importlib,json,pathlib,sys
for n in ['argparse','copy','gzip','hashlib','math','runpy','dataclasses','fractions','time','collections']:
 importlib.import_module(n)
expected=['/usr/lib/python313.zip','/usr/lib/python3.13','/usr/lib/python3.13/lib-dynload','/usr/local/lib/python3.13/dist-packages','/usr/lib/python3/dist-packages']
assert sys.path==expected,sys.path
assert sys.modules['sitecustomize'].__file__=='/usr/lib/python3.13/sitecustomize.py'
absent={n:importlib.util.find_spec(n) is None for n in ['apport_python_hook','usercustomize']}
assert all(absent.values()),absent
origins={n:getattr(m,'__file__',None)for n,m in sorted(sys.modules.items())if getattr(m,'__file__',None)}
assert all(pathlib.Path(p).is_relative_to('/usr/lib/python3.13')for p in origins.values()),origins
ps=json.loads(sys.argv[1]);out=[]
for p in ps:
 p=pathlib.Path(p);s=importlib.machinery.PathFinder.find_spec(p.stem,[str(p.parent)]);assert s is not None and pathlib.Path(s.origin)==p;out.append({'module':p.stem,'origin':s.origin})
print(json.dumps({'custom':out,'startup':{'sys_path':sys.path,'observed_stdlib_origins':origins,'absent_hooks':absent,'system_site_startup':True,'upstream_modules_imported':False}}))
"""
 resolution=json.loads(subprocess.check_output([str(PYTHON),'-I','-B','-c',probe,json.dumps([str(p)for p in custom])],cwd=EVID if EVID.exists()else HERE,env=env(EVID/'home'),text=True))
 return plan,{'utc':now(),'status':'PASS_FIXED_SOURCE_RUNTIME_GUARD','head':HEAD,'driver_sha256':sha(__file__),'plan_sha256':sha(HERE/'CK_GENERATION_RESOURCE_PROPOSAL.json'),'input_inventory_sha256':sha(HERE/'CK_GENERATION_INPUTS.json'),'pinned_files':len(rows),'resolved_custom_modules':resolution['custom'],'runtime_startup':resolution['startup'],'output_absent_required':require_absent,'source_execution':False}
def tree_size(root):
 total=0
 if not root.exists():return total
 for p in root.rglob('*'):
  if p.is_symlink():raise ValueError('unexpected output symlink: '+str(p))
  if p.is_file():total+=p.stat().st_size
 return total
def group_sample(pgid):
 result=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   st=(p/'stat').read_text();fields=st[st.rfind(')')+2:].split()
   if int(fields[2])!=pgid:continue
   status={line.split(':',1)[0]:line.split(':',1)[1].strip()for line in(p/'status').read_text().splitlines()if':'in line}
   get=lambda k:int(status.get(k,'0 kB').split()[0])*1024
   result.append({'pid':int(p.name),'state':fields[0],'vm_peak_bytes':get('VmPeak'),'rss_bytes':get('VmRSS'),'rss_peak_bytes':get('VmHWM'),'threads':int(status.get('Threads','0'))})
  except(FileNotFoundError,ProcessLookupError,PermissionError):continue
 return result
def terminate(proc):
 try:os.killpg(proc.pid,signal.SIGKILL)
 except ProcessLookupError:pass
 proc.wait()
def install_owner_signal_handlers():
 def stop(signum,frame):raise SystemExit(128+signum)
 for sig in (signal.SIGTERM,signal.SIGHUP):signal.signal(sig,stop)
def limits():
 os.setsid()
 resource.setrlimit(resource.RLIMIT_AS,(4294967296,4294967296))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 resource.setrlimit(resource.RLIMIT_FSIZE,(134217728,134217728))
def run_child(argv,log,deadline,job_review_seconds=480):
 cpu_before=resource.getrusage(resource.RUSAGE_CHILDREN)
 proc=None;start=time.monotonic();started=now();peaks={};samples=0;max_group_rss=0;max_group_vm=0;reason=None
 try:
  with log.open('xb')as f:
   proc=subprocess.Popen(argv,cwd=OUT,env=env(EVID/'home'),stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits)
   while True:
    rows=group_sample(proc.pid);samples+=1
    max_group_rss=max(max_group_rss,sum(r['rss_bytes']for r in rows));max_group_vm=max(max_group_vm,sum(r['vm_peak_bytes']for r in rows))
    for r in rows:
     old=peaks.get(r['pid'],{});peaks[r['pid']]={k:max(old.get(k,0),r[k])for k in ['vm_peak_bytes','rss_peak_bytes','threads']}
    if any(r['vm_peak_bytes']>=3758096384 for r in rows):reason='REVIEW_VM'
    elif time.monotonic()-start>=600:reason='HARD_JOB_WALL'
    elif time.monotonic()>=deadline:reason='HARD_TOTAL_WALL'
    elif time.monotonic()-start>=job_review_seconds:reason='REVIEW_JOB_WALL'
    elif tree_size(EVID)>536870912:reason='OUTPUT_DIRECTORY_LIMIT'
    if reason:terminate(proc);break
    if proc.poll()is not None:break
    time.sleep(.1)
   code=proc.wait()
  remaining=[r for r in group_sample(proc.pid)if r['state']!='Z']
  if remaining:reason=reason or'UNEXPECTED_REMAINING_PROCESS';terminate(proc)
  cpu_after=resource.getrusage(resource.RUSAGE_CHILDREN)
  return {'cpu_user_seconds':cpu_after.ru_utime-cpu_before.ru_utime,'cpu_system_seconds':cpu_after.ru_stime-cpu_before.ru_stime,'cpu_scope':'RUSAGE_CHILDREN delta for waited child and its accounted descendants','started_utc':started,'finished_utc':now(),'seconds':time.monotonic()-start,'pid':proc.pid,'exit_code':code,'stop_reason':reason,'samples':samples,'process_peaks':peaks,'peak_group_rss_bytes':max_group_rss,'max_sum_vmpeaks_bytes':max_group_vm,'aggregate_memory_cap_claimed':False,'log_sha256':sha(log),'argv':argv}
 finally:
  if proc is not None:terminate(proc)
def compare_content(path,expected):
 if payload_sha(path)!=expected:raise ValueError('generated content mismatch: '+str(path))
def artifacts(step,plan):
 rows=[]
 for name in step['outputs']:
  p=Path(name)
  if not p.is_file() or p.is_symlink():raise ValueError('missing output: '+name)
  rows.append({'path':name,'sha256':sha(p),'bytes':p.stat().st_size})
 if 'required_output_content_sha256'in step:compare_content(Path(step['outputs'][0]),step['required_output_content_sha256'])
 local=OUT/'ck-local';expect=plan['output_identity']['mandatory_semantic_hashes']
 if step['name']=='ck-localize':compare_content(local/'CANONICAL-WORD.json.gz',expect['CANONICAL-WORD.json.gz'])
 if step['name']=='ck-emit':
  compare_content(local/'LOCAL-PROGRAMS.json.gz',expect['LOCAL-PROGRAMS.json.gz'])
  checks=read(local/'LOCAL-CHECKS.json');program=read(local/'LOCAL-PROGRAMS.json.gz')
  assert json_sha(checks)==expect['LOCAL-CHECKS.json']
  assert set(program)=={'forward','backward'}
  for key,events in program.items():assert len(events)==21559 and json_sha(events)==plan['output_identity']['orientation_event_hashes'][key]
 if step['name']=='ck-recipes':
  assert sha(local/'CLIFFORD-RECIPES.json')==plan['output_identity']['catalog_raw_required']
  assert json_sha(read(local/'CLIFFORD-RECIPES.json'))==expect['CLIFFORD-RECIPES.json']
  phase=read(local/'CLIFFORD-REVIEW.json')
  assert phase['canonical_word_sha256']==sha(local/'CANONICAL-WORD.json.gz') and phase['recipe_sha256']==sha(local/'CLIFFORD-RECIPES.json')
  seconds=phase.pop('seconds');assert type(seconds)in(int,float)and math.isfinite(seconds)and seconds>=0
  phase['canonical_word_sha256']=payload_sha(local/'CANONICAL-WORD.json.gz');phase['recipe_sha256']=json_sha(read(local/'CLIFFORD-RECIPES.json'))
  assert json_sha(phase)==expect['CLIFFORD-REVIEW.json']
 return rows
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--execute',action='store_true');ap.add_argument('--admission');ap.add_argument('--admission-sha256');args=ap.parse_args()
 plan,before=guard(True)
 if not args.execute:print(json.dumps(before,indent=2));return 0
 install_owner_signal_handlers()
 if not args.admission or not args.admission_sha256:raise ValueError('exact admission required')
 admission=Path(args.admission).resolve();exact(admission,args.admission_sha256);a=read(admission)
 assert a['authorized'] is True and a['driver_sha256']==sha(__file__) and a['plan_sha256']==PINS[HERE/'CK_GENERATION_RESOURCE_PROPOSAL.json']
 assert a['head']==HEAD and a['jobs']==[s['name']for s in plan['steps']] and a['max_attempts']==1
 for r in a['required_reviews']:exact(Path(r['path']),r['sha256'])
 assert a['required_reviews']
 EVID.mkdir(parents=True,exist_ok=True)
 held=[];handles=[];proc=None;result={'status':'FAIL_UNFINISHED','before':before,'jobs':[],'admission_sha256':args.admission_sha256}
 with (EVID/'owner.lock').open('a+')as owner:
  fcntl.flock(owner,fcntl.LOCK_EX|fcntl.LOCK_NB)
  try:
   inv,rows=records()
   for p in sorted({ROOT/r['path']for r in rows}|set(PINS)|{Path(__file__).resolve(),admission}):
    f=p.open('rb');fcntl.flock(f,fcntl.LOCK_SH);held.append(f)
   plan,before=guard(True);save('RUN_STARTED.json',{'utc':now(),'driver_sha256':sha(__file__),'admission_sha256':args.admission_sha256,'next_owner':'bank','attempt':1})
   OUT.mkdir();(EVID/'home').mkdir(exist_ok=False)
   spec=importlib.util.spec_from_file_location('accepted_shared_slots',SLOT);service=importlib.util.module_from_spec(spec);spec.loader.exec_module(service)
   requested=time.monotonic();result['requested_utc']=now();slot,handle,handles=service.acquire('ck_generation:'+HEAD);result.update(slot=slot,queue_seconds=time.monotonic()-requested,slot_acquired_utc=now());deadline=time.monotonic()+2100
   for step in plan['steps']:
    if time.monotonic()>=deadline:raise TimeoutError('total wall before job')
    guard(False);exact(admission,args.admission_sha256)
    assert sha(__file__)==a['driver_sha256']
    for r in a['required_reviews']:exact(Path(r['path']),r['sha256'])
    if 'required_input_content_sha256'in step:compare_content(Path(step['argv'][step['argv'].index('--input')+1]),step['required_input_content_sha256'])
    job=run_child(step['argv'],EVID/(step['name']+'.log'),deadline);job['name']=step['name'];result['jobs'].append(job);save(step['name']+'_PROCESS.json',job)
    guard(False)
    assert sha(__file__)==a['driver_sha256']
    if job['exit_code']!=0 or job['stop_reason']:raise RuntimeError('first failure/review stop: '+step['name'])
    job['artifacts']=artifacts(step,plan);save(step['name']+'_ARTIFACTS.json',job['artifacts'])
    actual={str(p)for p in OUT.rglob('*')if p.is_file()};allowed={p for s in plan['steps'][:len(result['jobs'])]for p in s['outputs']}
    assert actual==allowed,('unexpected/missing output',sorted(actual^allowed))
   guard(False);assert sha(__file__)==a['driver_sha256'];result['status']='PASS_EXACT_CK_ARTIFACT_MATERIALIZATION_WITH_INTRINSIC_CHECKS'
  except BaseException as exc:
   result.update(status='STOP_FAILURE_OR_REVIEW_NO_RETRY',exception_type=type(exc).__name__,exception=str(exc));raise
  finally:
   result['finished_utc']=now();result['driver_sha256']=sha(__file__)
   try:
    _,post=guard(False);result['post_guard']=post
    assert sha(__file__)==a['driver_sha256']
   except BaseException as exc:result['post_guard_error']=str(exc);result['status']='STOP_SOURCE_PRESERVATION_FAILURE'
   save('RESULT.json',result)
   for h in handles:h.close()
   for h in held:h.close()
 print(json.dumps(result,indent=2));return 0
if __name__=='__main__':raise SystemExit(main())
