from pathlib import Path
import re
B=Path('/workspace/shared/integer-mult-git/worktrees/bank')
P=B/'research/f19-label-recipe-coverage-proposal'
O=B/'research/current535-label-coverage-proposal'
s=(P/'F19CoverageStatement.lean').read_text()
# Preserve the accepted definition/proof bodies with explicit cardinality parameters.
s=s[s.index('abbrev Register'):s.index('/-- No retained event')]+s[s.index('/-- Only Boolean equality soundness'):s.index('theorem checkPilot_wellLabelled')]
s=s.replace('abbrev FrameLabel := Fin 983','abbrev FrameLabel (frameCount : Nat) := Fin frameCount')
s=s.replace('abbrev LabelEvent := LemmaG.Event Register FrameLabel CoefficientCode','abbrev LabelEvent (frameCount : Nat) := LemmaG.Event Register (FrameLabel frameCount) CoefficientCode')
for n in ['ChildKey','Row','SelectedData']:
 s=s.replace('structure '+n+' where','structure '+n+' (frameCount : Nat) where')
# Qualify bare type names, excluding declaration names and projections.
for n in ['FrameLabel','LabelEvent','ChildKey','Row','SelectedData']:
 s=re.sub(r'(?<![\w.])'+n+r'(?![\w.]| \(frameCount)',r'('+n+' frameCount)',s)
# Above does not touch declaration names because they have (frameCount).
s=s.replace('/-- These are canonical-frame labels, not boundary adapter/operator charts. -/', 'variable {frameCount : Nat}\n\n/-- Canonical labels only. The default label is supplied explicitly; no hidden finite-cardinality assumption. -/')
s=s.replace('def initialLabels (p : (SelectedData frameCount))', 'def initialLabels (zero : FrameLabel frameCount) (p : (SelectedData frameCount))')
s=s.replace('.getD 0 else 0','.getD zero else zero')
d=(P/'pilot/handoff/scaling_experiment/F19CoverageCheckDecomposition.lean').read_text()
d=d[d.index('def labelRowsB'):d.index('#print axioms')]
a=(P/'pilot/handoff/scaling_experiment/F19CoverageBoundary192.lean').read_text()
a=a[a.index('def supportedB'):a.index('private theorem supportedB_moves')]
v=(P/'pilot/handoff/child34/F19CoverageSparseValues.lean').read_text()
v=v[v.index('private theorem supported_moves'):v.index('#print axioms')].replace('Boundary192.supportedB','supportedB')
for name in ['FrameLabel','LabelEvent','ChildKey','Row','SelectedData']:
 d=re.sub(r'\b'+name+r'\b(?!\.)','('+name+' frameCount)',d)
 a=re.sub(r'\b'+name+r'\b(?!\.)','('+name+' frameCount)',a)
 v=re.sub(r'\b'+name+r'\b(?!\.)','('+name+' frameCount)',v)
s='''/- Parameterized canonical-frame coverage helper for the selected h=9 source.
The Boolean tests and proofs are generalized from the accepted f19 coverage modules.
PR509 Stream/WellLabelled: DreamingOfClouds (Claude-assisted), pinned unchanged.
No whole-stream, omitted-adapter, scalar endpoint or operator realization claim.
Apache-2.0. Prepared with OpenAI assistance. -/
import PR509Stream

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.CanonicalFrameCoverage

'''+s+d+a+v+'''#print axioms admissibleB_sound
#print axioms checkRows_wellLabelled
#print axioms checkRows_factor
#print axioms sparse_checkpoint
end CurrentMain.CanonicalFrameCoverage
'''
s=s.replace('((FrameLabel frameCount) frameCount)','(FrameLabel frameCount)')
(O/'CanonicalFrameCoverage.lean').write_text(s)
