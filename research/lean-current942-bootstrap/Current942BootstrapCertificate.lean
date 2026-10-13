import Current942NativeUpperAggregate

/-!
Exact seven-update PR942 T37 bootstrap arithmetic from pinned main
bbc600db2fc15007b7c914f4f2b2ed55fa909c87. The fixed adapter in
research/complex-t37-owners/prepare.py supplies the current assembler.
The native complex saving is the proposed finite input; PR589 bit saving
and initial saving are supplied finite inputs. The charged coefficient is
1024, matching the T37 prefix allowance. Each update, four-way minimum,
both ceiling candidates and maximum cutoff are independently kernel checked
when this source is compiled; this preparation is currently uncompiled.

Current beta=eta=10^-24 and strict offset10^-27 are explicit. Eta belongs to
later q/grid/outer formulas; no47-slack or all-size conclusion is asserted.
Supplier saving validity, native/bit recurrence interpretation, operator/profile
and physical realization remain separate. Author-checked conditional context:
kappa=1661960547713947/1000000000000000000=0.001661960547713947.
Attribution: PR942 fixed assembler adaptation and accepted rational interfaces.
Prepared with OpenAI assistance; no native evaluation or external oracle.
-/
namespace CurrentMain.Current942BootstrapCertificate
open Current942NativeUpperAggregate
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
def recordedShrink : Rat := ((416181814685169713942999333818185314830286057 : Rat) / 250000000000000000000000000000000000000000000000)
def chargedCoefficient : Nat := 1024

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
def checkpoint1 : Rat := ((103876247946161440080057377896962787857178473276730863994254679988695665724797891267551392751 : Rat) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap1 : Rat := ((169205725130988405692455557583540850393040973269136005745320011304334275202108732448607249 : Rat) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff1 : Int := 4911706737567
def linearCutoff1 : Int := 759430569
def recordedCutoff1 : Nat := 4911706737567
def checkpoint2 : Rat := ((26011292997477366986656878792457101305020878010848664852222677613549771476476241004222271952643119865936154167491325917634564236746086172807 : Rat) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap2 : Rat := ((70420345740134780579571179480871872000551651335147777322386450228523523758995777728047356880134063845832508674082365435763253913827193 : Rat) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff2 : Int := 1772336766424157901
def linearCutoff2 : Int := 456189183146
def recordedCutoff2 : Nat := 1772336766424157901
def checkpoint3 : Rat := ((6502840825148109499473010858275981414538244775392390493795702649060453144660444744286706848547783107151599400506699143998491130731245495164533318807457318600858499698341275955000144651999 : Rat) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap3 : Rat := ((29307667280886353732633164129684974865232609506204297350939546855339555255713293151452216892848400599493300856001508869268754504835466681192542681399141500301658724044999855348001 : Rat) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff3 : Int := 639528738471729375193491
def linearCutoff3 : Int := 274032386236272
def recordedCutoff3 : Nat := 639528738471729375193491
def checkpoint4 : Rat := ((1625710213601746876936692691495811940717507284067446528893393574196212339042034342219960054881347748442872399951361831885815513596006811905189220116151342105287875470455579035667642186915398248506444536803899484791834202080223886877943 : Rat) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap4 : Rat := ((12197318153148456231474445338297626088803471106606425803787660957965657780039945118652251557127600048638168114184486403993188094810779883848657894712124529544420964332357813084601751493555463196100515208165797919776113122057 : Rat) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff4 : Int := 230767095215447300436172576982
def linearCutoff4 : Int := 164610980445871992
def recordedCutoff4 : Nat := 230767095215447300436172576982
def checkpoint5 : Rat := ((406427553403480972470457017244506017394700391129416213445423233213154021978055025830448021702842353532361095082481824004888530004356192072783163172241249877818031162106510680932346219156278026208999865073792311541074992963542368580413232444225691185874017620930479561842203333740751 : Rat) / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap5 : Rat := ((5076302003269687315579119250836409646286554576766786845978021944974169551978297157646467638904917518175995111469995643807927216836827758750122181968837893489319067653780843721973791000134926207688458925007036457631419586767555774308814125982379069520438157796666259249 : Rat) / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff5 : Int := 83269834536965707586896522785415935
def linearCutoff5 : Int := 98881651382578877051
def recordedCutoff5 : Nat := 83269834536965707586896522785415935
def checkpoint6 : Rat := ((101606888350871510080450492122214609449413369591027364844514665453503726840271335469378032435904337180739310816325629889774994466744559587788721572892389831944588142322311042657474341021992812691943686727138963116500505097370720118433893800034094900168701553063549000947376245304622537456997967155749701687508656813694677208008807 : Rat) / 61035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap6 : Rat := ((2112664579610740789679074437293738260155485334546496273159728664530621967564095662819260689183674370110225005533255440412211278427107610168055411857677688957342525658978007187308056313272861036883499494902629279881566106199965905099831298446936450999052623754695377462543002032844250298312491343186305322791991193 : Rat) / 61035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff6 : Int := 30047027880383448577363131591267949447298
def linearCutoff6 : Int := 59398109127725926589642
def recordedCutoff6 : Nat := 30047027880383448577363131591267949447298
def checkpoint7 : Rat := ((25401722087717878047399515354675370480720123834301459117238230678240097544423754070673558407597137813240645080999367118185569781125616007693489164172440492770797245366869199496205505620356638937167352620756623487537852259814168118115963527897743737948573541399678233704713759901054310968219181698547664514178261166218891162436092280671878444412343826049897797210985799185303999 : Rat) / 15258789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap7 : Rat := ((879252578563479301401827886889947132761769321759902455576245929326441592402862186759354919000632881814430218874383992306510835827559507229202754633130800503794494379643361062832647379243376512462147740185831881884036472102256262051426458600321766295286240098945689031780818301452335485821738833781108837563907719328121555587656173950102202789014200814696001 : Rat) / 15258789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff7 : Int := 10842148173643272889999539096203012516204841615
def linearCutoff7 : Int := 35680384769249822678910235
def recordedCutoff7 : Nat := 10842148173643272889999539096203012516204841615

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

def recordedEndpoint : Rat := ((25401722087717878047399515354675370480720123834301459117238230678240097544423754070673558407597137813240645080999367118185569781125616007693489164172440492770797245366869199496205505620356638937167352620756623487537852259814168118115963527897743737948573541399678233704713759901054310968219181698547664514178261166218891162436092280671878444412343826049897797210985799185303999 : Rat) / 15258789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

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
end CurrentMain.Current942BootstrapCertificate
