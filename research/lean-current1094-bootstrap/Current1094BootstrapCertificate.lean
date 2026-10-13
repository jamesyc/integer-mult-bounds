import Current1094NativeUpperAggregate

/-!
Exact seven-update PR1094 T16 bootstrap arithmetic at pinned main
ce7ad1b6ab09452c3478723a2e96ed5ff212dc08, using the unchanged caller
research/gauge44-slots-t16/code/assemble.py with the pinned PR1094
rare-pattern OWNERS/PLAN/SPEC overlay.
The native, PR589 bit and initial savings are supplied finite inputs.
The source's complex charged coefficient is 512, giving linear numerator 1032.
This differs explicitly from the historical T37 coefficient 1024; the T37
source and accepted result are preserved, not repinned.

All seven updates, four-way minima, both separate integer ceilings and maximum
cutoffs retain the accepted rational proof bodies. Beta=eta=10^-24 and strict
offset 10^-27 are explicit. The endpoint theorem composes all seven updates.
This is source preparation; actual kernel acceptance requires a bounded check.

Author-checked conditional source context:
kappa=836330098538459/500000000000000000=0.001672660197076918.
Saving validity, Real enclosures, native/bit recurrence interpretation,
operator/profile/physical realization, the 47 outer slacks, precision/tape
and all-size multiplication remain separate.
Attribution: accepted PR942/PR799 rational interfaces, inherited bootstrap
arithmetic and PR1094 T16's pinned caller. Prepared with OpenAI assistance;
no supplier execution, native evaluation or external oracle is used.
-/
namespace CurrentMain.Current1094BootstrapCertificate
open Current1094NativeUpperAggregate
set_option Elab.async false

/-- Source minimum/maximum use exact comparisons and retain tie order. -/
def ratMin (x y : Rat) : Rat := if x ≤ y then x else y
def intMax (x y : Int) : Int := if x ≤ y then y else x

def nativeComplexSaving : Rat := bCurrent
def suppliedBitSaving : Rat := ((1733427039589844234749 : Rat) / 1000000000000000000000000)
def eta : Rat := ((1 : Rat) / 1000000000000000000000000)
def beta : Rat := ((1 : Rat) / 1000000000000000000000000)
def strictOffset : Rat := ((1 : Rat) / 1000000000000000000000000000)
def selectedShrink : Rat := ratMin suppliedBitSaving ((1-beta)*nativeComplexSaving) - strictOffset
def recordedShrink : Rat := ((67018507072324140916999892981492927675859083 : Rat) / 40000000000000000000000000000000000000000000000)
def chargedCoefficient : Nat := 512

def bootstrapStep (s old : Rat) : Rat := (1-s)*s+s*old
/-- The source's left-associated minimum of all four gap expressions. -/
def sourceGap (s old next : Rat) : Rat :=
  ratMin (ratMin (ratMin (s-next) (1-next-s)) (1-next-s*(1-old))) (1-s)
def quadraticCeiling (gap : Rat) : Int := Rat.ceil (36/(gap*gap))
def linearCeiling (gap : Rat) : Int := Rat.ceil (2*(4+(chargedCoefficient : Rat))/gap)
def sourceCutoff (gap : Rat) : Int := intMax (quadraticCeiling gap) (linearCeiling gap)

/-- The native complex branch is the smaller of the two supplied candidates. -/
theorem saving_minimum_is_native :
    ratMin suppliedBitSaving ((1-beta)*nativeComplexSaving) =
      (1-beta)*nativeComplexSaving ∧
    (1-beta)*nativeComplexSaving < suppliedBitSaving := by decide +kernel

theorem shrink_matches_literal : selectedShrink = recordedShrink := by decide +kernel

/-- Arithmetic domains only, without a validity theorem for either supplier. -/
theorem supplied_input_domains :
    0 < nativeComplexSaving ∧ 0 < suppliedBitSaving ∧
    0 < selectedShrink ∧ selectedShrink < suppliedBitSaving ∧
    selectedShrink < (1-beta)*nativeComplexSaving ∧ selectedShrink < 1 := by
  rw [shrink_matches_literal]
  decide +kernel

def checkpoint0 : Rat := ((384599 : Rat) / 10000000000)
def checkpoint1 : Rat := ((2676351903605968510955225199374139336419692211991205809803291212685832779316802617926399111 : Rat) / 1600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap1 : Rat := ((4388379286997125724770519885577770614671108008794190196708787314167220683197382073600889 : Rat) / 1600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff1 : Int := 4785575287428
def linearCutoff1 : Int := 376266474
def recordedCutoff1 : Nat := 4785575287428
def checkpoint2 : Rat := ((107229317213090343809558513333591284579279399862953574758040118663735837979673222607810293919010512865815663359806135729869323361652475213 : Rat) / 64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap2 : Rat := ((294102628281657641315436797399702095132937046425241959881336264162020326777392189706080989487134184336640193864270130676638347524787 : Rat) / 64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff2 : Int := 1704765459304159860
def linearCutoff2 : Int := 224574667646
def recordedCutoff2 : Nat := 1704765459304159860
def checkpoint3 : Rat := ((4289184432918425945204602612810811814242177218571549743614845366342624240747502661971213062645949901457815846541829576632569723585538319837683356531863935997754461046639237713138409679 : Rat) / 2560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap3 : Rat := ((19710319073483390538004735557012804093428450256385154633657375759252497338028786937354050098542184153458170423367430276414461680162316643468136064002245538953360762286861590321 : Rat) / 2560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff3 : Int := 607288590542446415285737
def linearCutoff3 : Int := 134037403968474
def recordedCutoff3 : Nat := 607288590542446415285737
def checkpoint4 : Rat := ((171567378103828844589295714015277247208277763194683861086506039620411038425241223225415374750246673707197993416981116984785025248834072957802186876854129419662928338294140179682651151779349930844098048754952574172587583050727264357 : Rat) / 102400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap4 : Rat := ((1320956158224012017344647641921489285316138913493960379588961574758776774584625249753326292802006583018883015214974751165927042197813123145870580337071661705859820317348848220650069155901951245047425827412416949272735643 : Rat) / 102400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff4 : Int := 216334411393790970429839007220
def linearCutoff4 : Int := 80000232666373616
def recordedCutoff4 : Nat := 216334411393790970429839007220
def checkpoint5 : Rat := ((6862695124205903501391156875228590725366338670593798130778146011247213048799329248276386353883527829505727811814785950491330293597981298780354995034957137345602662361138997814404555486275586374750298102671091066436586235588225737165500314750679738457912869234305574310420604631 : Rat) / 4096000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap5 : Rat := ((88528509632166076285068641631428606201869221853988752786951200670751723613646116472170494272188185214049508669706402018701219645004965042862654397337638861002185595444513724413625249701897328908933563413764411774262834499685249320261542087130765694425689579395369 : Rat) / 4096000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff5 : Int := 77064806225479172206224871399132079
def linearCutoff5 : Int := 47748143706060195179
def recordedCutoff5 : Nat := 77064806225479172206224871399132079
def checkpoint6 : Rat := ((274507804968239675262983012766557017278150386312268407171634736048569145063436078292308834161068093358180970305987390168436997280846699807340390028600235262791714958423212022381294505311826715320340799973882750272976631732616603410592302985180390981719778700426281993988599893959139653519462414098149103287619172127213213373 : Rat) / 163840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap6 : Rat := ((5933048548885638014482168417655731592828365263951430854936563921707691165838931906641819029694012609831563002719153300192659609971399764737208285041576787977618705494688173284679659200026117249727023368267383396589407697014819609018280221299573718006011400106040860346480537585901850896712380827872786786627 : Rat) / 163840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff6 : Int := 27452795513701194724472919763925196307643
def linearCutoff6 : Int := 28498482459200106410301
def recordedCutoff6 : Nat := 27452795513701194724472919763925196307643
def checkpoint7 : Rat := ((10980312198729587247443638409953866657622706241115298082593784379580155884572917200344472124669626723797186984560821354838219435018476566046245535271824370260204012228829867664389945037956713272090789374737043715481558118907727540190325040178552489169072639330426685561304684411155742187127395446448215283528354225333356459993467204656154640201711847789658794506759116959 : Rat) / 6553600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap7 : Rat := ((397624056133934612790045917604701917406215620419844115427082799655527875330373276202813015439178645161780564981523433953754464728175629739795987771170132335610054962043286727909210625262956284518441881092272459809674959821447510830927360669573314438695315588844257812872604553551784716471645774666643540006532795343845359798288152210341205493240883041 : Rat) / 6553600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff7 : Int := 9779509200503493187646549135972282547372018449
def linearCutoff7 : Int := 17009320979618655619702172
def recordedCutoff7 : Nat := 9779509200503493187646549135972282547372018449

/-- Twelve source arithmetic obligations, with both ceiling candidates exposed. -/
def StageFacts (old next gap : Rat) (quad linear : Int) (cutoff : Nat) : Prop :=
  bootstrapStep selectedShrink old = next ∧
  sourceGap selectedShrink old next = gap ∧
  gap = selectedShrink-next ∧
  quadraticCeiling gap = quad ∧ linearCeiling gap = linear ∧
  sourceCutoff gap = (cutoff : Int) ∧
  old < next ∧ next < selectedShrink ∧ selectedShrink < 1-next ∧
  0 < gap ∧ 36 ≤ (cutoff : Rat)*gap*gap ∧
  2*(4+(chargedCoefficient : Rat)) ≤ (cutoff : Rat)*gap

theorem stage1_certificate :
    StageFacts checkpoint0 checkpoint1 recordedGap1
      quadraticCutoff1 linearCutoff1 recordedCutoff1 := by
  unfold StageFacts
  rw [shrink_matches_literal]
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  decide +kernel

theorem stage2_certificate :
    StageFacts checkpoint1 checkpoint2 recordedGap2
      quadraticCutoff2 linearCutoff2 recordedCutoff2 := by
  unfold StageFacts
  rw [shrink_matches_literal]
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  decide +kernel

theorem stage3_certificate :
    StageFacts checkpoint2 checkpoint3 recordedGap3
      quadraticCutoff3 linearCutoff3 recordedCutoff3 := by
  unfold StageFacts
  rw [shrink_matches_literal]
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  decide +kernel

theorem stage4_certificate :
    StageFacts checkpoint3 checkpoint4 recordedGap4
      quadraticCutoff4 linearCutoff4 recordedCutoff4 := by
  unfold StageFacts
  rw [shrink_matches_literal]
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  decide +kernel

theorem stage5_certificate :
    StageFacts checkpoint4 checkpoint5 recordedGap5
      quadraticCutoff5 linearCutoff5 recordedCutoff5 := by
  unfold StageFacts
  rw [shrink_matches_literal]
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  decide +kernel

theorem stage6_certificate :
    StageFacts checkpoint5 checkpoint6 recordedGap6
      quadraticCutoff6 linearCutoff6 recordedCutoff6 := by
  unfold StageFacts
  rw [shrink_matches_literal]
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  decide +kernel

theorem stage7_certificate :
    StageFacts checkpoint6 checkpoint7 recordedGap7
      quadraticCutoff7 linearCutoff7 recordedCutoff7 := by
  unfold StageFacts
  rw [shrink_matches_literal]
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  refine And.intro ?_ ?_
  · decide +kernel
  decide +kernel

def bootstrapEndpoint : Rat :=
  bootstrapStep selectedShrink (bootstrapStep selectedShrink (bootstrapStep selectedShrink (bootstrapStep selectedShrink (bootstrapStep selectedShrink (bootstrapStep selectedShrink (bootstrapStep selectedShrink (checkpoint0)))))))

def recordedEndpoint : Rat := ((10980312198729587247443638409953866657622706241115298082593784379580155884572917200344472124669626723797186984560821354838219435018476566046245535271824370260204012228829867664389945037956713272090789374737043715481558118907727540190325040178552489169072639330426685561304684411155742187127395446448215283528354225333356459993467204656154640201711847789658794506759116959 : Rat) / 6553600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

/-- Seven ordered source updates reach the exact last serialized exponent. -/
theorem bootstrap_endpoint_matches_certificate : bootstrapEndpoint = recordedEndpoint := by
  unfold bootstrapEndpoint
  rw [stage1_certificate.1, stage2_certificate.1, stage3_certificate.1, stage4_certificate.1, stage5_certificate.1, stage6_certificate.1, stage7_certificate.1]
  rfl

#print axioms saving_minimum_is_native
#print axioms shrink_matches_literal
#print axioms supplied_input_domains
#print axioms stage1_certificate
#print axioms stage2_certificate
#print axioms stage3_certificate
#print axioms stage4_certificate
#print axioms stage5_certificate
#print axioms stage6_certificate
#print axioms stage7_certificate
#print axioms bootstrap_endpoint_matches_certificate
end CurrentMain.Current1094BootstrapCertificate
