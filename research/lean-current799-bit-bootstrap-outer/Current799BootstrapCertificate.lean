import Current799NativeUpperAggregate

/-!
Exact seven-update current PR799 native bootstrap arithmetic from pinned
mainf567884 gauge44-frames-x/assemble.py:206-214. The complex saving is the
accepted native input; the PR589 bit saving, initial saving and charged512
coefficient remain supplied finite inputs. Each update, four-way minimum,
both ceiling candidates and maximum cutoff are independently kernel checked.
The accepted seven-stage proof structure is reused with freshly bound literals.

Current beta=eta=10^-24 and strict offset10^-27 are explicit. Eta belongs to
later q/grid/outer formulas, and no47-slack or all-size conclusion is asserted.
Supplier saving validity, native/bit recurrence interpretation, operator/profile
and physical realization remain separate. Author-checked conditional context:
kappa=1661634653669567/1000000000000000000=0.001661634653669567.
Attribution: PR799 assembler and accepted rational certificate interfaces.
Prepared with OpenAI assistance; no native evaluation or external oracle.
-/
namespace CurrentMain.Current799BootstrapCertificate
open Current799NativeUpperAggregate
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
def recordedShrink : Rat := ((1664400278850482327912997335599721149517672087 : Rat) / 1000000000000000000000000000000000000000000000000)
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
def checkpoint1 : Rat := ((1661694063230529326247532356645485399750266170039269531711785379343151425711090279684341064431 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap1 : Rat := ((2706215619953001665464978954235749767405916960730468288214620656848574288909720315658935569 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff1 : Int := 4915613269871
def linearCutoff1 : Int := 381344337
def recordedCutoff1 : Nat := 4915613269871
def checkpoint2 : Rat := ((1664395774624449848606118109081612800417555412728409229233976555299169102538556343554743785838812295689182240936273476235983048891262797237497 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap2 : Rat := ((4504226032479306879226518108349100116674271590770766023444700830897461443656445256214161187704310817759063726523764016951108737202762503 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff2 : Int := 1774443388201110908
def linearCutoff2 : Int := 229118164266
def recordedCutoff2 : Nat := 1774443388201110908
def checkpoint3 : Rat := ((1664400271353647263448837295018467124425208413594237908149934888894096192815429490764050024800458679059027214960474531848638144132391112171796758786265424732549416673306883775035445906646239 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap3 : Rat := ((7496835064464160040581254025092463673405762091850065111105903807184570509235949975199541320940972785039525468151361855867608887828203241213734575267450583326693116224964554093353761 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff3 : Int := 640540491097945923200390
def linearCutoff3 : Int := 137658090531003
def recordedCutoff3 : Nat := 640540491097945923200390
def checkpoint4 : Rat := ((1664400278838004593541207113969535954758019270267770779313961129516569400931880314744999809525696603675857759086715768645767201504480763837543439937593454654577518223849349509364750104703819566529019297080899914844923331971077776713830793 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap4 : Rat := ((12477734371790221630185194759652816732229220686038870483430599068119685255000190474303396324142240913284231354232798495519236162456560062406545345422481776150650490635249895296180433470980702919100085155076668028922223286169207 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff4 : Int := 231222998414134964443595932879
def linearCutoff4 : Int := 82707322439332836
def recordedCutoff4 : Nat := 231222998414134964443595932879
def checkpoint5 : Rat := ((1664400278850461559968429505706906587497238985538039012262175588126498806276381165153033657001547779070641699436525194780426476209691681940282473892298718217285655168264697680871404051461094577665898690765273544407125305811914155467253661971388582031354844824285582358680309945377174991 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap5 : Rat := ((20767944567829892814562020433101461960987737824411873501193723618834846966342998452220929358300563474805219573523790308318059717526107701281782714344831735302319128595948538905422334101309234726455592874694188085844532746338028611417968645155175714417641319690054622825009 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff5 : Int := 83467127743916184993039472927586044
def linearCutoff5 : Int := 49691966223686665636
def recordedCutoff5 : Nat := 83467127743916184993039472927586044
def checkpoint6 : Rat := ((1664400278850482293346824605752287850234388192503565223790894004712955019553215384500863883980062227072173466200909582482818123897182251882924907284854573339508840739045397799228969538093282908249608223630529871248583746466917361288397080052695234980949710320194666289819632000439529936606578221788166191701357794224206842838755176217 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap6 : Rat := ((34566172729847433299283283894496434776209105995287044980446784615499136116019937772927826533799090417517181876102817748117075092715145426660491159260954602200771030461906717091750391776369470128751416253533082638711602919947304765019050289679805333710180367999560470063393421778211833808298642205775793157161244823783 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff6 : Int := 30130053937546965452116011965235164002719
def linearCutoff6 : Int := 29855778597926221658328
def recordedCutoff6 : Nat := 30130053937546965452116011965235164002719
def checkpoint7 : Rat := ((1664400278850482327855465388069369143586435121053665030166869338178305424940270385079134329116690147254011450076912281701518726346197744658918873837396308276631963042457010885411191508006979982651540317326402465054441388797398774857639401059131162911435288263366987395086938852427088199438502394213829112107506626899267880828713436710996442241952007389033258759957576109887307154879 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def recordedGap7 : Rat := ((57531947530352005931236965946334969833130661821694575059729614920865670883309852745988549923087718298481273653802255341081126162603691723368036957542989114588808491993020017348459682673597534945558611202601225142360598940868837088564711736633012604913061147572911800561497605786170887892493373100732119171286563289003557758047992610966741240042423890112692845121 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
def quadraticCutoff7 : Int := 10876379418071676456390609457427077833228788828
def linearCutoff7 : Int := 17937859646686738313700712
def recordedCutoff7 : Nat := 10876379418071676456390609457427077833228788828

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

def recordedEndpoint : Rat := ((1664400278850482327855465388069369143586435121053665030166869338178305424940270385079134329116690147254011450076912281701518726346197744658918873837396308276631963042457010885411191508006979982651540317326402465054441388797398774857639401059131162911435288263366987395086938852427088199438502394213829112107506626899267880828713436710996442241952007389033258759957576109887307154879 : Rat) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)

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
end CurrentMain.Current799BootstrapCertificate
