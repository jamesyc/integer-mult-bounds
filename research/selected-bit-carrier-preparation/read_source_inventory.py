from pathlib import Path
import collections,datetime,gzip,hashlib,io,json,re,resource,subprocess,time
resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(15,15))
start=time.monotonic();G=Path('/workspace/shared/integer-mult-git/worktrees/signed');prefix='research/e8-bit-carrier-skeleton';P=G/prefix;UP='c3a9a436b84fe44fdc223a5784d84736d1c2d3c7'
sha=lambda b:hashlib.sha256(b).hexdigest()
def strict(b):
 assert len(b)<=16*1024**2
 def pairs(xs):
  d={}
  for k,v in xs:assert k not in d;d[k]=v
  return d
 return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError(x)))
manifest=strict((G/'research/community-pr531-audit/SOURCE.json').read_bytes())['files']
tree=subprocess.check_output(['git','-C',str(G),'ls-tree','-r',UP,'--',prefix]).decode().splitlines()
assert len(tree)==94
package=[]
for row in tree:
 meta,name=row.split('\t');mode,kind,blob=meta.split();assert kind=='blob'
 p=G/name;b=p.read_bytes();h=sha(b);assert h==manifest[name]
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
 package.append(dict(path=name,bytes=len(b),sha256=h,upstream_git_blob=blob))
assert len(list(P.rglob('*')))>94
listed={}
for line in (P/'MANIFEST.sha256').read_text().splitlines():
 h,name=line.split('  ',1);assert name not in listed;listed[name]=h
assert len(listed)==93 and set(listed)=={str((G/x['path']).relative_to(P))for x in package if not x['path'].endswith('/MANIFEST.sha256')}
for name,h in listed.items():assert sha((P/name).read_bytes())==h
selected=strict((G/'certificates/selected-result.json').read_bytes());assert selected['reviewed_dependency_heads']['493']==UP
integration=strict((G/'docs/research/community-pr531-integration.json').read_bytes());assert integration['reviewed_heads']['493']==UP
for path,h in integration['receipts'].items():assert sha((G/path).read_bytes())==h
expected=strict((P/'EXPECTED.json').read_bytes());copied=strict((G/'research/direct-delivery504-global/inputs/PR493-EXPECTED.json').read_bytes());assert expected==copied
assembly=strict((G/'research/community-pr531-audit/direct-ASSEMBLY.json').read_bytes())
assert assembly['bit_result_sha256']==sha((G/'research/direct-delivery504-global/inputs/PR493-EXPECTED.json').read_bytes())
assert assembly['bit_lower']==expected['eleven']['bit_lower'] and assembly['bit_template_sha256']==expected['eleven']['emitted_program_sha256']
with gzip.open(P/'data/bit/bitE8mut-r489.json.gz','rb')as z:b=z.read(16*1024**2+1)
w=strict(b);assert sha(b)==expected['word']['content_sha256']
assert set(w)=={'A','B','C','D','R','coords','final','form','format','frames','h','lines','ret','scatter','start','v'}
assert [w['h'],w['v'],w['R']]==[8,120,489]and w['format']=='bitE8/1+mut'and w['form']=='<x,y>/2'
v=120;n=729;is_y=lambda r:120<=r<240;is_z=lambda r:0<=r<n and not is_y(r)
integer=lambda x:type(x)is int
assert len(w['lines'])==120 and all(len(x)==8 and all(integer(a)for a in x)for x in w['lines'])
assert len(w['frames'])==672 and all(all(integer(i)and 0<=i<120 for i in f)for f in w['frames'])
assert w['frames'][0]==[]and w['frames'][1]==list(range(120)) and w['lines'][:8]==[[2*int(i==j)for j in range(8)]for i in range(8)]
for name in ['start','final']:assert len(w[name])==n and all(integer(f)and 0<=f<672 for f in w[name])
assert all(w['start'][r]==0 for r in range(120,n))
assert all(w['final'][r]==1 for r in range(n)if is_z(r))
assert all(w['frames'][w['start'][r]]==[r]for r in range(120))
assert w['ret']==list(range(720,729))and len(w['scatter'])==120 and all(all(integer(i)and 0<=i<9 for i in row)for row in w['scatter'])
maxarity=0
for sec in ['D','A','B','C']:
 for gate in w[sec]:
  assert len(gate)==3;f,d,src=gate;assert integer(f)and 0<=f<672 and integer(d)and 0<=d<n and isinstance(src,list)and all(integer(s)and 0<=s<n for s in src)
  assert len(set([d]+src))==1+len(src);maxarity=max(maxarity,len(src))
  if is_z(d):assert all(is_z(s)for s in src)
assert all(f==0 and is_y(d)and all(s>=240 for s in ss)for f,d,ss in w['D'])
assert all(is_z(d)for f,d,ss in w['A'])and all(is_y(d)for f,d,ss in w['B'])
projected=[[1,d,list(ss)]for sec in ['A','B']for f,d,ss in w[sec]if is_z(d)]
assert w['C']==list(reversed(projected))
writes=[(i,f,d,ss)for i,(f,d,ss)in enumerate(w['A'])if d<120]
assert len(writes)==577 and len({d for i,f,d,ss in writes})==117
shape=dict(format=w['format'],geometry_dimension=8,source_ports=120,helpers=489,registers=729,frames=672,phase_gate_counts={sec:len(w[sec])for sec in ['D','A','B','C']},retained_totals=9,source_destination_gates=577,rewritten_sources=117,max_gate_sources=maxarity,zero_frame_id=0,full_frame_id=1,full_frame_literal='List.range120',first_eight_rows='2 times the8x8 identity',source_and_helper_final_full=609,first_mutable_source_gate=dict(A_index=writes[0][0],gate=w['A'][writes[0][0]],matching_C_index=len(w['A'])-1-writes[0][0]),full_cleanup_reversal_gate_count=len(w['C']))
support_paths=['certificates/selected-result.json','docs/research/community-pr531-review.md','docs/research/community-pr531-integration.json','research/community-pr531-audit/SOURCE.json','research/community-pr531-audit/bit-INTERFACE.json','research/community-pr531-audit/bit-AUDIT.json','research/community-pr531-audit/bit-COLUMNS11.json','research/community-pr531-audit/bit-RESULT.json','research/community-pr531-audit/dependency-bindings.json','research/community-pr531-audit/direct-ASSEMBLY.json','research/direct-delivery504-global/inputs/PR493-EXPECTED.json','research/direct-delivery504-global/code/assemble.py']
support=[dict(path=s,sha256=sha((G/s).read_bytes()),bytes=(G/s).stat().st_size)for s in support_paths]
result=dict(status='SOURCE_IDENTITY_AND_STRUCTURAL_READBACK_ONLY',completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),selected_upstream_head=UP,worktree_head=subprocess.check_output(['git','-C',str(G),'rev-parse','HEAD']).decode().strip(),package_count=94,package_bytes=sum(x['bytes']for x in package),package_files=package,support_files=support,word_compressed_sha256=sha((P/'data/bit/bitE8mut-r489.json.gz').read_bytes()),word_decoded_sha256=sha(b),word_decoded_bytes=len(b),shape=shape,not_performed=['supplier execution','generator execution','compiler','rational rank/Gram evaluation','F2 operator replay','physical hosting replay'],elapsed_seconds=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024)
print(json.dumps(result,indent=2))
