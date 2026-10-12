import Current588NativeUpperAggregate

/-!
Exact seven-update native bootstrap arithmetic from pinned main9594's PR588
assemble.py:177-185. The source complex saving is the accepted native input;
the PR543 bit saving, initial saving and charged coefficient remain supplied
finite inputs. This proof checks each update and all source min/ceiling choices.
It does not import the historical six-update bootstrap or its coefficient6464.

Current beta=eta=10^-24 and strict offset10^-27 are explicit. Eta belongs to
the subsequent q/grid/outer formulas; the present endpoint proof does not use
eta to claim any of the47 outer slacks. All-size bootstrap interpretation,
bit-supplier validity, native recurrence validity and physical realization
remain separate. Author-checked conditional source context:
kappa=400569730495803/250000000000000000=0.001602278921983212.
Attribution: PR588 complex-571-free4fc8/assemble.py and accepted rational
certificate interfaces. Prepared with OpenAI assistance; kernel checks only.
-/
namespace CurrentMain.Current588BootstrapCertificate
open Current588NativeUpperAggregate
set_option Elab.async false

/-- Source minimum/maximum use exact comparisons and retain tie order. -/
def ratMin (x y : Rat) : Rat := if x ≤ y then x else y
def intMax (x y : Int) : Int := if x ≤ y then y else x

def nativeComplexSaving : Rat := bCurrent
def suppliedBitSaving : Rat := ((413456747036699736067 : Rat) / 250000000000000000000000)
def eta : Rat := ((1 : Rat) / 1000000000000000000000000)
def beta : Rat := ((1 : Rat) / 1000000000000000000000000)
def strictOffset : Rat := ((1 : Rat) / 1000000000000000000000000000)
def selectedShrink : Rat := ratMin suppliedBitSaving ((1-beta)*nativeComplexSaving) - strictOffset
def recordedShrink : Rat := ((802425169927850686730998697574830072149313269 : Rat) / 500000000000000000000000000000000000000000000000)
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
def checkpoint1 : Rat := ((400584129406488057387737969284071753474066988067064234129053337341985194315638054811700533639 : Rat) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap1 : Rat := ((628455557437285977761379503343282600589646432935765870946662658014805684361945188299466361 : Rat) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff1 : Int := 5696831524240
def linearCutoff1 : Int := 410530223
def recordedCutoff1 : Nat := 5696831524240
def checkpoint2 : Rat := ((200605788193405202966421519790127460271143656688025302514122276929441589413535431133159783512732353885290763690884531568361880978134683555891 : Rat) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap2 : Rat := ((504288557468716328154603580057766184660561974697485877723070558410586464568866840216487267646114709236309115468431638119021865316444109 : Rat) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff2 : Int := 2211893940700616220
def linearCutoff2 : Int := 255805923196
def recordedCutoff2 : Nat := 2211893940700616220
def checkpoint3 : Rat := ((100303145836327504421869441006403375833634570304154126484093996360338569031064089994938738621337571493116180702908984366017114971159931879586881631145111130735812047671991246678162629417679 : Rat) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap3 : Rat := ((404653831419505396190450383185029588320845873515906003639661430968935910005061261378662428506883819297091015633982885028840068120413118368854888869264187952328008753321837370582321 : Rat) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff3 : Int := 858806300325169436063060
def linearCutoff3 : Int := 159395500528779
def recordedCutoff3 : Nat := 858806300325169436063060
def checkpoint4 : Rat := ((50151573120165963501248666135621427545046382716024393925836678349483328251413175723428720474697956383959326842888864970855973130716622292969366056306970222580514076287715956029414895715412618353444859334055078055641038590754877217882651 : Rat) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap4 : Rat := ((324704419438752462805451964285696596475606074163321650516671748586824276571279525302043616040673157111135029144026869283377707030633943693029777419485923712284043970585104284587381646555140665944921944358961409245122782117349 : Rat) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff4 : Int := 333446485795149429388746130312
def linearCutoff4 : Int := 99321099650395035
def recordedCutoff4 : Nat := 333446485795149429388746130312
def checkpoint5 : Rat := ((25075786560245073409344764834164763086944171576718218300598035596514917421685921276195999421279976233048384713349133240929242114111202296570060481262056967710321428900039224880424092677069719478007406562286939536054284261919156219469452016773972424640332120947953154856976555879196119 : Rat) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap5 : Rat := ((260550998944465048676667721868079531781699401964403485082578314078723804000578720023766951615286650866759070757885888797703429939518737943032289678571099960775119575907322930280521992593437713060463945715738080843780530547983226027575359667879052046845143023444120803881 : Rat) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff5 : Int := 129466398706013538017570622191819779
def linearCutoff5 : Int := 61888075905772870528
def recordedCutoff5 : Nat := 129466398706013538017570622191819779
def checkpoint6 : Rat := ((12537893280122666771099175046723108279295084553391872608766022891875428359507731538619431770351791098935229694944331305753350212647487047445712193066527784265978878069798641469062127041169362624705557359266491050771405828553329051807286268634600499059543851515500475531558992465615693323675966405333432934125365668401574509620003011 : Rat) / 7812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap6 : Rat := ((209072679602883611598037935274733127391233977108124571640492268461380568229648208901064770305055668694246649787352512952554287806933472215734021121930201358530937872958830637375294442640733508949228594171446670948192713731365399500940456148484499524468441007534384306676324033594666567065874634331598425490379996989 : Rat) / 7812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff6 : Int := 50267581479931405426802488054218388617837
def linearCutoff6 : Int := 38563144717492772157668
def recordedCutoff6 : Nat := 50267581479931405426802488054218388617837
def checkpoint7 : Rat := ((6268946640061333489918162144345744974396398340693676493303110154528572564869381116277460525329249193372264935997537518132526716892237961562985670532321436940893800199878008913489070726829527323659196010342624902765293417753262065282761228543055677829658158300658486624083662143444444839606867582962244531100704935261797682397864633690608271401939176916224716785231781389362252959 : Rat) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap7 : Rat := ((167765180457614964270111573368823506696889845471427435130618883722539474670750806627735064002462481867473283107762038437014329467678563059106199800121991086510929273170472676340803989657375097234706582246737934717238771456944322170341841699341513375916337856555555160393132417037755468899295064738202317602135366309391728598060823083775283214768218610637747041 : Rat) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff7 : Int := 19517262958548448609973324447307700375769019230
def linearCutoff7 : Int := 24029122068142591706722327
def recordedCutoff7 : Nat := 19517262958548448609973324447307700375769019230

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

def recordedEndpoint : Rat := ((6268946640061333489918162144345744974396398340693676493303110154528572564869381116277460525329249193372264935997537518132526716892237961562985670532321436940893800199878008913489070726829527323659196010342624902765293417753262065282761228543055677829658158300658486624083662143444444839606867582962244531100704935261797682397864633690608271401939176916224716785231781389362252959 : Rat) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

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
end CurrentMain.Current588BootstrapCertificate
