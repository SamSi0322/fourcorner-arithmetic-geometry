import CriticalBoundaryTower

noncomputable section
namespace FourCorner.CriticalBoundaryFibres
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open CriticalBoundaryTower CriticalRadicalField CriticalElliptic23 CriticalSignPoints
open RationalPlaceFibreHom RationalPlaceTower RationalLineEvaluation QuadraticRationalPlaceFibre ResiduePlaceEvaluation
variable {k : Type*} [Field k]
set_option maxHeartbeats 2000000

/-- The two actual roots of one are exactly the original two signs. -/
def signRoots (h2 : (2:k)≠0) (d : k) (hd : d=1) : Bool ≃ {z:k // z^2=d} :=
  Equiv.ofBijective (fun e => ⟨sign e,(sign_sq e).trans hd.symm⟩) (by
    constructor
    · intro e f hef
      exact sign_injective h2 (congrArg Subtype.val hef)
    · intro z
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show z.val^2=(1:k)^2 by rw [z.property,hd,one_pow]) with hz|hz
      · refine ⟨false,Subtype.ext ?_⟩
        simpa only [sign,Bool.false_eq_true,if_false] using hz.symm
      · refine ⟨true,Subtype.ext ?_⟩
        simpa only [sign,if_true] using hz.symm)

@[simp] theorem signRoots_inverse (h2 : (2:k)≠0) (d : k) (hd : d=1) (z : {z:k // z^2=d}) :
    sign ((signRoots h2 d hd).symm z)=z.val :=
  congrArg Subtype.val ((signRoots h2 d hd).apply_symm_apply z)

abbrev linePlace (e : Bool) : Place k (RatFunc k) := placeOfPoint k (sign e)
abbrev FirstFibre (i : k) (e : Bool) :=
  {w : Place k (First i) // w.restrict (RatFunc k)=linePlace (k:=k) e ∧ w.IsRational}
abbrev SecondFibre (i : k) (w : Place k (First i)) :=
  {z : Place k (Full i) // z.restrict (First i)=w ∧ z.IsRational}
abbrev FullFibre (i : k) (e : Bool) :=
  {w : Place k (Full i) // w.restrict (RatFunc k)=linePlace (k:=k) e ∧ w.IsRational}

def firstAt (i : k) (e : Bool) : (linePlace (k:=k) e).toValuationSubring :=
  polynomialAt (sign e) (CriticalSquareclasses.qB i)
def secondAtLine (i : k) (e : Bool) : (linePlace (k:=k) e).toValuationSubring :=
  polynomialAt (sign e) (CriticalSquareclasses.qC i)

@[simp] theorem firstAt_evaluate (i : k) (e : Bool) :
    evaluate (linePlace e) (rational (sign e)) (firstAt i e)=1 := by
  rw [firstAt,evaluate_polynomialAt]
  simp [CriticalSquareclasses.qB,CriticalSquareclasses.quadratic,sign_sq]
@[simp] theorem secondAtLine_evaluate (i : k) (e : Bool) :
    evaluate (linePlace e) (rational (sign e)) (secondAtLine i e)=1 := by
  rw [secondAtLine,evaluate_polynomialAt]
  simp [CriticalSquareclasses.qC,CriticalSquareclasses.quadratic,sign_sq]

theorem firstAt_unit (i : k) (e : Bool) : IsUnit (firstAt i e) := by
  apply (ResidueValuationFacts.evaluate_nonzero_iff_unit (linePlace e) (rational (sign e)) _).mp
  rw [firstAt_evaluate];exact one_ne_zero
 theorem secondAtLine_unit (i : k) (e : Bool) : IsUnit (secondAtLine i e) := by
  apply (ResidueValuationFacts.evaluate_nonzero_iff_unit (linePlace e) (rational (sign e)) _).mp
  rw [secondAtLine_evaluate];exact one_ne_zero

theorem firstAt_square (i : k) (e : Bool) : firstRoot i^2=
    algebraMap (RatFunc k) (First i) (firstAt i e : RatFunc k) := by
  rw [firstAt,polynomialAt_coe]
  exact first_square i

/-- Two actual first-stage rational places over either original line sign. -/
def firstFibreEquiv (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Bool) :
    FirstFibre i e ≃ Bool := by
  letI := first_separable i h2
  exact (rationalFibreRootEquiv (linePlace e) (rational (sign e)) (firstAt i e) (firstRoot i)
    (firstAt_square i e) (first_generates i) (first_degree i hi h2) (firstAt_unit i e) h2).trans
    (signRoots h2 _ (firstAt_evaluate i e)).symm

def secondAt (i : k) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e) : w.val.toValuationSubring := by
  letI := first_separable i h2
  exact baseInclusion (linePlace e) w.val w.property.1 (secondAtLine i e)

theorem secondAt_coe (i : k) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e) :
    (secondAt i h2 e w : First i)=algebraMap (RatFunc k) (First i) (radicandC k i) := by
  letI := first_separable i h2
  unfold secondAt
  rw [baseInclusion_coe,secondAtLine,polynomialAt_coe]

theorem secondAt_unit (i : k) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e) : IsUnit (secondAt i h2 e w) := by
  letI := first_separable i h2
  exact (secondAtLine_unit i e).map (baseInclusion (linePlace e) w.val w.property.1).toRingHom

theorem secondAt_evaluate (i : k) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e) :
    evaluate w.val w.property.2 (secondAt i h2 e w)=1 := by
  letI := first_separable i h2
  unfold secondAt
  rw [evaluate_baseInclusion (linePlace e) (rational (sign e)),secondAtLine_evaluate]

theorem secondAt_square (i : k) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e) : c k i^2=
    algebraMap (First i) (Full i) (secondAt i h2 e w : First i) := by
  rw [secondAt_coe]
  exact second_square i

/-- The second quadratic contributes two actual rational places over each
actual first-stage place, not a formal list of coordinate sign tuples. -/
def secondFibreEquiv (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e) :
    SecondFibre i w.val ≃ Bool := by
  letI := second_separable i h2
  exact (rationalFibreRootEquiv w.val w.property.2 (secondAt i h2 e w) (c k i)
    (secondAt_square i h2 e w) (second_generates i) (second_degree i hi h2) (secondAt_unit i h2 e w) h2).trans
    (signRoots h2 _ (secondAt_evaluate i h2 e w)).symm

/-- The first label is the actual residue of the original first root. -/
theorem firstFibre_sign (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e)
    (R : w.val.toValuationSubring) (hR : (R:First i)=firstRoot i) :
    sign (firstFibreEquiv i hi h2 e w)=evaluate w.val w.property.2 R := by
  letI := first_separable i h2
  unfold firstFibreEquiv
  rw [Equiv.trans_apply,signRoots_inverse,rationalFibreRootEquiv_apply]
  congr 1
  apply Subtype.ext
  simpa only [rootAtPlace_coe] using hR.symm

/-- The second label is the actual residue of the original c coordinate. -/
theorem secondFibre_sign (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Bool)
    (w : FirstFibre i e)
    (z : SecondFibre i w.val)
    (R : z.val.toValuationSubring) (hR : (R:Full i)=c k i) :
    sign (secondFibreEquiv i hi h2 e w z)=evaluate z.val z.property.2 R := by
  letI := second_separable i h2
  unfold secondFibreEquiv
  rw [Equiv.trans_apply,signRoots_inverse,rationalFibreRootEquiv_apply]
  congr 1
  apply Subtype.ext
  simpa only [rootAtPlace_coe] using hR.symm

/-- Relabel a dependent pair using two genuine binary equivalences. -/
def dependentBinaryEquiv {X : Type*} {Y : X → Type*}
    (e : X ≃ Bool) (f : ∀x,Y x ≃ Bool) : (Σx,Y x) ≃ Bool×Bool :=
  (Equiv.sigmaEquivProdOfEquiv f).trans (Equiv.prodCongr e (Equiv.refl Bool))

/-- Four actual rational places over each line sign, via the two actual
quadratic field steps and their root-evaluation equivalences. -/
def lineFibreEquiv (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Bool) :
    FullFibre i e ≃ Bool×Bool := by
  letI := first_separable i h2
  letI := second_separable i h2
  letI := CriticalActualRamification.separable i h2
  exact (rationalTowerFibreEquiv (F:=RatFunc k) (E:=First i) (L:=Full i) (linePlace e)).trans
    (dependentBinaryEquiv (firstFibreEquiv i hi h2 e) (secondFibreEquiv i hi h2 e))

/-- Both labels retain the original b,c residue evaluations at the SAME
actual full-field place. Arbitrary integral representatives are permitted. -/
theorem lineFibre_coordinates (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Bool)
    (w : FullFibre i e) (B C : w.val.toValuationSubring)
    (hB : (B:Full i)=b k i) (hC : (C:Full i)=c k i) :
    sign (lineFibreEquiv i hi h2 e w).1=evaluate w.val w.property.2 B ∧
    sign (lineFibreEquiv i hi h2 e w).2=evaluate w.val w.property.2 C := by
  letI := first_separable i h2
  letI := second_separable i h2
  letI := CriticalActualRamification.separable i h2
  let v : FirstFibre i e := ⟨w.val.restrict (First i),by rw [restrict_trans,w.property.1],
    restrict_isRational w.val w.property.2⟩
  let z : SecondFibre i v.val := ⟨w.val,rfl,w.property.2⟩
  change sign (firstFibreEquiv i hi h2 e v)=evaluate w.val w.property.2 B ∧
    sign (secondFibreEquiv i hi h2 e v z)=evaluate w.val w.property.2 C
  constructor
  · let R := rootAtPlace (linePlace e) (firstAt i e) (firstRoot i) (firstAt_square i e)
      v.val v.property.1
    have hr : (R:First i)=firstRoot i := rootAtPlace_coe _ _ _ _ _ _
    have hb : B=baseInclusion v.val w.val rfl R := by
      apply Subtype.ext
      rw [baseInclusion_coe,hr]
      exact hB
    rw [hb,evaluate_baseInclusion v.val v.property.2 w.val rfl w.property.2]
    exact firstFibre_sign i hi h2 e v R hr
  · exact secondFibre_sign i hi h2 e v z C hC

#print axioms lineFibre_coordinates

#print axioms lineFibreEquiv
#print axioms firstFibre_sign
#print axioms secondFibre_sign

#print axioms firstFibreEquiv
#print axioms secondFibreEquiv
end FourCorner.CriticalBoundaryFibres
