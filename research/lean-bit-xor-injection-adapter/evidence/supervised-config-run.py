import datetime, hashlib, json, os, pathlib, re, resource, shutil, signal, subprocess, time
STAGE=pathlib.Path(__file__).resolve().parent
RUNTIME=STAGE.parent/'runtime'/'lean-4.21.0-linux'
LEAN=RUNTIME/'bin'/'lean'
STANDARD={'propext','Classical.choice','Quot.sound'}
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path):
 with path.open('rb') as inp:return hashlib.file_digest(inp,'sha256').hexdigest()
core_path=STAGE/'metadata'/'OFFICIAL_CORE_MANIFEST.json'
core=json.loads(core_path.read_bytes())
config_path=STAGE/'metadata'/'RUN_CONFIG.json'
assert sha(config_path)=='8a6360e48b608a23ee546faa2f063b3e314958fed98ab9229aaa03a981e5bf60'
config=json.loads(config_path.read_bytes())
assert config['format']=='bounded-core-local-scope-v1'
rows=config['fresh_modules'];retained=config['retained_modules'];all_rows=retained+rows
assert rows and len(all_rows)==config['local_total'] and 317+len(all_rows)==config['total_modules']
local_names=[r['module'] for r in all_rows];assert len(local_names)==len(set(local_names))
assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',n) for n in local_names)
assert all(r['file']==r['module']+'.lean' and isinstance(r['expected_probes'],list) for r in all_rows)
assert sum(len(r['expected_probes']) for r in rows)==config['fresh_probe_count']
assert all(set(p['axioms'])<=STANDARD for r in all_rows for p in r['expected_probes'])
protected_metadata={str(p):sha(p) for p in (STAGE/'metadata').iterdir() if p.is_file()}
successful={str(STAGE/'objects'/(r['module']+'.olean')):r['artifacts']['objects']['sha256'] for r in retained}
receipts=[]

def skip_space_comments(text,pos):
 while pos<len(text):
  if text[pos].isspace():pos+=1
  elif text.startswith('--',pos):
   end=text.find('\n',pos);pos=len(text) if end<0 else end+1
  elif text.startswith('/-',pos):
   depth=1;pos+=2
   while depth:
    assert pos<len(text),'unterminated official source comment'
    if text.startswith('/-',pos):depth+=1;pos+=2
    elif text.startswith('-/',pos):depth-=1;pos+=2
    else:pos+=1
  else:break
 return pos

def actual_imports(text):
 pos=skip_space_comments(text,0);has_prelude=False
 if re.match(r'module\b',text[pos:]):pos=skip_space_comments(text,pos+len('module'))
 if re.match(r'prelude\b',text[pos:]):pos+=len('prelude');has_prelude=True
 result=[]
 while True:
  pos=skip_space_comments(text,pos);checkpoint=pos
  if re.match(r'private\b',text[pos:]):pos=skip_space_comments(text,pos+len('private'))
  if not re.match(r'import\b',text[pos:]):pos=checkpoint;break
  pos=skip_space_comments(text,pos+len('import'))
  if re.match(r'all\b',text[pos:]):pos=skip_space_comments(text,pos+len('all'))
  m=re.match(r'[A-Za-z_][A-Za-z0-9_.]*',text[pos:]);assert m,'empty actual official import statement'
  result.append(m.group());pos+=len(m.group())
 return result,has_prelude

def guard(label):
 start=time.monotonic();assert sha(core_path)=='2c27354193fc7b11079b61116ab8e9c80485903845bda48ddf3c66057fed2cb1'
 assert sha(LEAN)=='cbf5fd536e142ef1beaccf33f788fd8a7f3f29fb214e75c11319a8d8677b4b2b' and LEAN.stat().st_size==8992
 assert core['root_modules']==['Init'] and len(core['ordered_modules'])==core['module_count']==317
 assert core['edge_count']==sum(len(row['imports']) for row in core['ordered_modules'])==1077
 seen=set();checked=[]
 for row in core['ordered_modules']:
  assert row['module'] not in seen and set(row['imports'])<=seen;seen.add(row['module'])
  result={'module':row['module'],'ordered_imports':row['imports']}
  for kind,suffix,prefix in [('source','.lean','src/lean'),('object','.olean','lib/lean')]:
   relative=pathlib.Path(prefix)/pathlib.Path(*row['module'].split('.')).with_suffix(suffix)
   assert str(relative)==row[kind]['file'];path=RUNTIME/relative
   assert path.is_file() and path.stat().st_size==row[kind]['bytes'] and sha(path)==row[kind]['sha256'],(row['module'],kind)
   result[kind+'_actual_path']=str(path);result[kind+'_sha256']=row[kind]['sha256'];result[kind+'_bytes']=path.stat().st_size
  parsed,prelude=actual_imports((RUNTIME/row['source']['file']).read_text())
  assert prelude and parsed==row['imports'],(row['module'],parsed,row['imports'],prelude)
  result['ordered_imports_match_actual_source']=True;checked.append(result)
 assert sum(r['source_bytes'] for r in checked)==5050982 and sum(r['object_bytes'] for r in checked)==84918424
 local_seen=set(seen);local_imports=[]
 for row in all_rows:
  assert row['module'] not in local_seen and set(row['imports'])<=local_seen
  source=STAGE/'sources'/row['file'];assert source.stat().st_size==row['bytes'] and sha(source)==row['sha256']
  imports,_=actual_imports(source.read_text());assert imports==row['imports'],(row['module'],imports)
  local_imports.append({'module':row['module'],'imports':imports,'source_path':str(source)})
  local_seen.add(row['module'])
 assert len(local_seen)==config['total_modules']
 terminal=config['retained_terminal'];tp=pathlib.Path(terminal['path'])
 assert tp.stat().st_size==terminal['bytes'] and sha(tp)==terminal['sha256']
 for row in retained:
  assert set(row['artifacts'])=={'sources','objects','logs','receipts'}
  for artifact in row['artifacts'].values():
   path=pathlib.Path(artifact['path']);assert path.is_file() and path.stat().st_size==artifact['bytes'] and sha(path)==artifact['sha256']
  prior=json.loads(pathlib.Path(row['artifacts']['receipts']['path']).read_bytes())
  assert prior['status']=='PASS' and prior['source_sha256']==row['sha256']==row['artifacts']['sources']['sha256']
  assert prior['object_sha256']==row['artifacts']['objects']['sha256'] and prior['raw_log_sha256']==row['artifacts']['logs']['sha256']
  assert prior['complete_ordered_axiom_records']==row['expected_probes']
  assert prior['lean_binary_sha256']==sha(LEAN) and prior['official_core_manifest_sha256']==sha(core_path)
  copied=STAGE/'objects'/(row['module']+'.olean')
  assert copied.stat().st_size==row['artifacts']['objects']['bytes'] and sha(copied)==row['artifacts']['objects']['sha256']
 for path,expected in protected_metadata.items():assert sha(pathlib.Path(path))==expected,path
 for path,expected in successful.items():assert sha(pathlib.Path(path))==expected,path
 assert {p.name for p in (STAGE/'objects').iterdir()}=={pathlib.Path(p).name for p in successful if pathlib.Path(p).parent==STAGE/'objects'}
 assert shutil.disk_usage('/workspace').free>=8*1024**3
 report={'verified_utc':now(),'pairs_checked':317,'ordered_edges_checked':1077,'actual_source_import_order_matches':True,'runtime_sha256':sha(LEAN),'protected_metadata_count':len(protected_metadata),'successful_predecessor_artifacts_checked':len(successful),'retained_quadruples_checked':len(retained),'local_import_order':local_imports,'total_modules_checked':len(local_seen),'configuration_sha256':sha(config_path),'guard_seconds':time.monotonic()-start,'actual_pairs':checked}
 (STAGE/'logs'/(label+'-core-guard.json')).write_text(json.dumps(report,indent=2)+'\n')
 return {k:v for k,v in report.items() if k!='actual_pairs'}

def limits():resource.setrlimit(resource.RLIMIT_AS,(4294967296,4294967296))

env=os.environ.copy();env.update(LEAN_PATH=str(STAGE/'objects'),MIMALLOC_ARENA_RESERVE='64MiB',LEAN_NUM_THREADS='1')
assert {p.name for p in (STAGE/'objects').iterdir()}=={r['module']+'.olean' for r in retained}
assert not list((STAGE/'logs').iterdir()) and not list((STAGE/'receipts').iterdir())
assert not (STAGE/'FRESH_RESULT.json').exists()
initial=guard('initial');print(json.dumps({'initial_guard':initial}),flush=True)
result={'kind':'fresh-core-only-signed-owner-handoff-verification','status':'RUNNING','stage':str(STAGE),'started_utc':now(),'modules_planned':len(rows),'axiom_records_required':config['fresh_probe_count'],'retained_local_outputs':len(retained),'configuration_sha256':sha(config_path),'retained_modules':[r['module'] for r in retained],'fresh_receipts':[]}
(STAGE/'FRESH_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
for row in rows:
 module=row['module'];source=STAGE/'sources'/row['file'];output=STAGE/'objects'/(module+'.olean');assert not output.exists();pre_guard=guard(module+'-before')
 for dep in row['imports']:
  relative=pathlib.Path(*dep.split('.')).with_suffix('.olean')
  choices=[STAGE/'objects'/relative,RUNTIME/'lib'/'lean'/relative]
  expected=choices[0] if dep in local_names else choices[1]
  assert next((p for p in choices if p.is_file()),None)==expected,(module,dep,'first match')
  if dep in local_names:assert str(expected) in successful,(module,dep,'unaccepted local input')
 command=[str(LEAN),'-s65536','-j1','-o',str(output),str(source)]
 raw=STAGE/'logs'/(module+'.raw.log');measurements=STAGE/'logs'/(module+'.resources.jsonl')
 started=now();clock=time.monotonic();vm=rss=threads=samples=0;stop=None;rusage=None
 with raw.open('wb') as log,measurements.open('w') as metrics:
  proc=subprocess.Popen(command,cwd=STAGE/'sources',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
  while True:
   try:
    status=(pathlib.Path('/proc')/str(proc.pid)/'status').read_text();vals={}
    for key in ['VmPeak','VmHWM','VmRSS','Threads']:
     m=re.search(r'^'+key+r':\s+(\d+)',status,re.M);vals[key]=int(m.group(1)) if m else 0
    vm=max(vm,vals['VmPeak']*1024);rss=max(rss,vals['VmHWM']*1024);threads=max(threads,vals['Threads']);samples+=1
    metrics.write(json.dumps({'elapsed_seconds':time.monotonic()-clock,'vm_peak_bytes':vals['VmPeak']*1024,'rss_hwm_bytes':vals['VmHWM']*1024,'threads':vals['Threads']})+'\n')
   except FileNotFoundError:pass
   elapsed=time.monotonic()-clock
   if elapsed>=60:stop='HARD_WALL_60_SECONDS'
   elif elapsed>45 or vm>3758096384:stop='REVIEW_THRESHOLD'
   if stop:
    try:os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError:pass
   pid,status,rusage0=os.wait4(proc.pid,os.WNOHANG)
   if pid:
    proc.returncode=os.waitstatus_to_exitcode(status);rusage=rusage0;break
   time.sleep(.005)
 elapsed=time.monotonic()-clock;finished=now();rss=max(rss,rusage.ru_maxrss*1024)
 text=raw.read_bytes().decode(errors='replace');pattern=r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])"
 probes=[{'declaration':m[1],'axioms':[] if m[2] is None else [a.strip() for a in m[2].split(',') if a.strip()]} for m in re.finditer(pattern,text,re.S)]
 standard=all(set(p['axioms'])<=STANDARD for p in probes)
 probe_match=probes==row['expected_probes'] if 'expected_probes' in row else [p['declaration'] for p in probes]==row['expected_probe_declarations'] and len(probes)==2
 forbidden='sorryAx' in text or "declaration uses 'sorry'" in text
 passed=proc.returncode==0 and not stop and not forbidden and standard and probe_match and output.is_file()
 post_guard_error=None
 # Freeze a successful object's exact bytes before the preservation guard.
 if passed:successful[str(output)]=sha(output)
 try:post_guard=guard(module+'-after')
 except Exception as exc:post_guard_error=repr(exc);post_guard=None;passed=False
 receipt={'module':module,'output_provenance':'FRESH_CURRENT_EXECUTOR_RUN','status':'PASS' if passed else 'REVIEW_STOP' if stop=='REVIEW_THRESHOLD' else 'FAIL','started_utc':started,'finished_utc':finished,'command':command,'cwd':str(STAGE/'sources'),'environment_overrides':{k:env[k] for k in ['LEAN_PATH','MIMALLOC_ARENA_RESERVE','LEAN_NUM_THREADS']},'hard_wall_seconds':60,'rlimit_as_bytes':4294967296,'review_wall_seconds':45,'review_vm_peak_bytes':3758096384,'exit_code':proc.returncode,'stop_reason':stop,'compile_seconds':elapsed,'peak_vm_bytes':vm,'peak_rss_bytes':rss,'kernel_peak_rss_bytes':rusage.ru_maxrss*1024,'peak_threads':threads,'samples':samples,'sample_interval_seconds':.005,'user_cpu_seconds':rusage.ru_utime,'system_cpu_seconds':rusage.ru_stime,'source_bytes':source.stat().st_size,'source_sha256':sha(source),'lean_binary_sha256':sha(LEAN),'official_core_manifest_sha256':sha(core_path),'official_core_pairs':317,'official_core_ordered_edges':1077,'imports':row['imports'],'complete_ordered_axiom_records':probes,'expected_probes_match':probe_match,'standard_only_axioms':standard,'forbidden_axioms_or_sorry':forbidden,'raw_log_path':str(raw),'raw_log_sha256':sha(raw),'object_path':str(output) if output.exists() else None,'object_bytes':output.stat().st_size if output.exists() else None,'object_sha256':sha(output) if output.exists() else None,'pre_guard':pre_guard,'post_guard':post_guard,'post_guard_error':post_guard_error}
 rp=STAGE/'receipts'/(module+'.json');rp.write_text(json.dumps(receipt,indent=2)+'\n');receipts.append(receipt)
 result['fresh_receipts'].append({'module':module,'path':str(rp),'sha256':sha(rp),'status':receipt['status']});result['status']='RUNNING' if passed else receipt['status'];(STAGE/'FRESH_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(receipt),flush=True)
 if not passed:raise SystemExit(2)
 successful[str(raw)]=sha(raw);successful[str(rp)]=sha(rp)
final_guard=guard('final');ordered=[probe for receipt in receipts for probe in receipt['complete_ordered_axiom_records']];assert len(receipts)==len(rows) and len(ordered)==config['fresh_probe_count'] and all(set(r['axioms'])<=STANDARD for r in ordered)
result.update(status='PASS',finished_utc=now(),modules_successful=len(rows),complete_ordered_axiom_records=ordered,axiom_records_observed=len(ordered),final_guard=final_guard,peak_vm_bytes=max(r['peak_vm_bytes'] for r in receipts),peak_rss_bytes=max(r['peak_rss_bytes'] for r in receipts),compile_seconds=sum(r['compile_seconds'] for r in receipts));(STAGE/'FRESH_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'final_result':result}),flush=True)
