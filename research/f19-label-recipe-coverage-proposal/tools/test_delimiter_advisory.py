"""Local deterministic fixtures only; never invoke Lean or repository suppliers."""
import importlib.util,json,time,hashlib,gzip,resource
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('advisory',HERE/'lean_delimiter_advisory.py');a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
TESTS=[
 ('balanced','theorem t (x : Nat) : [x] = [x] := by rfl','ADVISORY_NO_ASCII_IMBALANCE'),
 ('nested_comments','/- ) outer /- [ nested -/ } -/ def x := (1)','ADVISORY_NO_ASCII_IMBALANCE'),
 ('line_comment','-- ) ] }\ndef x := { y := (2) }','ADVISORY_NO_ASCII_IMBALANCE'),
 ('string','def s := "( [ } \\" ]"','ADVISORY_NO_ASCII_IMBALANCE'),
 ('chars',r"def a := '('; def b := '\''; def c := '\n'; def d := 'λ'",'ADVISORY_NO_ASCII_IMBALANCE'),
 ('quoted_identifier','def «name ( ] /- \" » := 1','ADVISORY_NO_ASCII_IMBALANCE'),
 ('identifier_primes',"theorem foo' (x' : Nat) : x' = x' := rfl",'ADVISORY_NO_ASCII_IMBALANCE'),
 ('unicode_tuple','def t := ⟨(1), [2]⟩','ADVISORY_NO_ASCII_IMBALANCE'),
 ('unicode_notation','exact ‹h›','INCONCLUSIVE'),
 ('mismatch','def x := (1]','ADVISORY_DELIMITER_ISSUES'),
 ('interpolation','def x := s!"value {(1)}"','INCONCLUSIVE'),
 ('backtick','def x := `(foo)','INCONCLUSIVE'),
 ('raw_string','def x := r#"(abc"#','INCONCLUSIVE'),
 ('unsupported_char',"def x := 'ab'",'INCONCLUSIVE'),
 ('unterminated_comment','/- nested /- -/','INCONCLUSIVE'),
]
start=time.perf_counter();results=[]
for name,text,want in TESTS:
 r=a.scan(text);assert r['status']==want,(name,r);results.append({'name':name,'expected':want,'actual':r})
W=Path('/workspace/scratch/c569c316cd54');Q=W/'recovery_20261011/post114_reconstruction/bank/f19_coverage_child5';P=HERE.parent/'pilot/handoff/child5'
failed=Q/'failure01/F19CoverageChild5Check.lean';fixed=P/'F19CoverageChild5Check.lean'
assert hashlib.sha256(failed.read_bytes()).hexdigest()=='fa3e28e359bd8d301f51e8d534e1b697e89a72937ddcbd216c56fd51f82c19c5'
assert hashlib.sha256(fixed.read_bytes()).hexdigest()=='70bfe1a72494b9284c4a9c6648483690d3649854810685cf461bccedd403e58a'
bad=a.check_file(failed);good=a.check_file(fixed);assert bad['status']=='ADVISORY_DELIMITER_ISSUES' and bad['issue_count']==8;assert good['status']=='ADVISORY_NO_ASCII_IMBALANCE'
# A source-only literal fixture for the next24 rows, not a proof/candidate admission.
decoder=HERE.parent/'pilot/decode_pilot.py';assert hashlib.sha256(decoder.read_bytes()).hexdigest()=='89be739f32fecd831140c33f9d85027c6b2d69c17b6efc57e6faed591bc84946'
spec=importlib.util.spec_from_file_location('literal_decoder',decoder);x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x)
ROOT=HERE.parents[2];pins=json.loads((HERE.parent/'SOURCE_PINS.json').read_text());inputs={};input_pins=[]
for r in pins['inputs']:
 if r['role']!='decoder input':continue
 p=ROOT/r['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];input_pins.append(r)
 with gzip.open(p,'rb') if p.suffix=='.gz' else p.open('rb') as f:b=f.read(x.MAX+1)
 inputs[p.name]=x.json_raw(b)
children=inputs['CLIFFORD-RECIPES.json']['children'];lookup={(c['old'],c['new']):(i,c['rank'])for i,c in enumerate(children)}
rows=[x.decode_row(i,inputs['LOCAL-PROGRAMS.json.gz']['forward'][i],lookup)for i in range(11260,11284)];assert all(r is not None for r in rows)
text='/- ADVISORY LEXICAL FIXTURE ONLY. No kernel/finite coverage claim. -/\nimport F19CoverageStatement\nnamespace CurrentMain.F19SelectedCoverage.DelimiterFixture\ndef next24 : List Row := [\n'+',\n'.join(x.lean_row(r)for r in rows)+'\n]\nend CurrentMain.F19SelectedCoverage.DelimiterFixture\n'
fixture=Q/'advisory_next24.lean.txt';assert not fixture.exists() or fixture.read_text()==text;fixture.write_text(text);next_result=a.check_file(fixture);assert next_result['status']=='ADVISORY_NO_ASCII_IMBALANCE'
report={'status':'ADVISORY_FIXTURE_TESTS_PASS','helper_sha256':hashlib.sha256((HERE/'lean_delimiter_advisory.py').read_bytes()).hexdigest(),'tests':results,'failed_fixture':bad,'repaired_fixture':good,'next_source_fixture':next_result,'next_source_scope':'Only24 forward literal rows11260..11283, no theorem/activation/compiler/finite predicate evaluation. Emitted by pinned decoder after exact input hashes.','inputs':input_pins,'elapsed_seconds':time.perf_counter()-start,'maxrss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'baseline_wasted_compile_seconds':11.83733003999805,'limits':'Standalone fixtures/emission20CPU/30wall/512MiBAS; scanner1MiB and depth4096.','use':'Local optional advisory only; never reject valid Lean or replace independent scientific/API/compiler review.'}
out=Q/'DELIMITER_ADVISORY_TEST_RESULT_V2.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'report':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'elapsed_seconds':report['elapsed_seconds'],'next_scan_seconds':next_result['elapsed_seconds'],'failed_opens':bad['issue_count']}))
