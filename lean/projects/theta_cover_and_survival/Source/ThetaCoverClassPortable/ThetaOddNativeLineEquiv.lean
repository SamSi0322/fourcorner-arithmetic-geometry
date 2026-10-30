import ThetaCoverClassPortable.ThetaNativeDualCanonicalLines

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve KaehlerDifferential
namespace FourCorner.ThetaOddNativeLineEquiv
open ThetaDGeometricModel ThetaGaloisCanonicalCorrespondence ThetaNativeDualCanonicalLines
open ThetaOddThetaCanonicalLines ThetaActualOddThetaClasses DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

abbrev OddPic := {c : ActualPic // IsOddThetaClass c}

/-- A DIRECT intrinsic condition on an actual native dual-plane point: its
true canonical section has twice an effective divisor of odd genuine ell.
This definition does not mention Pic classes, a displayed list, or an image. -/
def IsOddCanonicalLine (L : NativeDual) : Prop :=
  ∃(a : Fin 3→K)(ha : a≠0)(B : ActualDivisor),L=dualOf a ha ∧ 0≤B ∧ Odd (ell B) ∧
    canonicalDivisorOf (planeToField_ne_zero ha)=(2:ℕ) • B
abbrev OddNativeLine := {L : NativeDual // IsOddCanonicalLine L}

 theorem odd_class_of_line_data {a : Fin 3→K} (ha : a≠0) {B : ActualDivisor}
    (hell : Odd (ell B)) (hcan : canonicalDivisorOf (planeToField_ne_zero ha)=(2:ℕ) • B) :
    IsOddThetaClass (divisorClass B) := by
  constructor
  · calc
      (2:ℕ) • divisorClass B=divisorClass ((2:ℕ) • B) := by simp only [two_nsmul];rfl
      _=divisorClass (canonicalDivisorOf (planeToField_ne_zero ha)) := by rw [hcan]
      _=canonicalClass K field := (canonicalClass_eq (planeToField_ne_zero ha)).symm
  · rwa [picEll_class]

 def chosenData (c : OddPic) :
    {p : ActualDivisor×(Fin 3→K) // CanonicalRepresentative c.val p.1 p.2 ∧
      Divisor.degree p.1=2 ∧ ell p.1=1} := by
  have h : ∃p : ActualDivisor×(Fin 3→K),CanonicalRepresentative c.val p.1 p.2 ∧
      Divisor.degree p.1=2 ∧ ell p.1=1 := by
    obtain ⟨B,a,hA,hdeg,hell⟩ := exists_representative c.val c.property
    exact ⟨(B,a),hA,hdeg,hell⟩
  exact ⟨h.choose,h.choose_spec⟩
 def chosenB (c : OddPic) : ActualDivisor := (chosenData c).val.1
 def chosenCoefficients (c : OddPic) : Fin 3→K := (chosenData c).val.2
 theorem chosenRepresentative (c : OddPic) :
    CanonicalRepresentative c.val (chosenB c) (chosenCoefficients c) := (chosenData c).property.1
 def chosenNonzero (c : OddPic) : chosenCoefficients c≠0 := (chosenRepresentative c).choose
 theorem chosenSpec (c : OddPic) :
    0≤chosenB c ∧ divisorClass (chosenB c)=c.val ∧
      canonicalDivisorOf (planeToField_ne_zero (chosenNonzero c))=(2:ℕ) • chosenB c :=
  (chosenRepresentative c).choose_spec

 def lineOf (c : OddPic) : OddNativeLine :=
  ⟨dualOf (chosenCoefficients c) (chosenNonzero c),by
    refine ⟨chosenCoefficients c,chosenNonzero c,chosenB c,rfl,
      (chosenSpec c).1,?_,(chosenSpec c).2.2⟩
    change Odd (ell (chosenData c).val.1)
    rw [(chosenData c).property.2.2]
    decide⟩

 theorem lineOf_val (c : OddPic) : (lineOf c).val=
    dualOf (chosenCoefficients c) (chosenNonzero c) := rfl

 theorem lineOf_injective : Function.Injective lineOf := by
  intro c d h
  obtain ⟨hB,hBc,hcanB⟩ := chosenSpec c
  obtain ⟨hE,hEd,hcanE⟩ := chosenSpec d
  have hline : dualOf (chosenCoefficients c) (chosenNonzero c)=
      dualOf (chosenCoefficients d) (chosenNonzero d) := congrArg Subtype.val h
  have hcan := canonical_divisor_eq_of_dual_eq (chosenNonzero c) (chosenNonzero d) hline
  have hBE : chosenB c=chosenB d :=
    double_divisor_injective (hcanB.symm.trans (hcan.trans hcanE))
  apply Subtype.ext
  exact hBc.symm.trans ((congrArg divisorClass hBE).trans hEd)

 theorem lineOf_surjective : Function.Surjective lineOf := by
  intro L
  obtain ⟨a,ha,B,hL,hB,hell,hcan⟩ := L.property
  let c : OddPic := ⟨divisorClass B,odd_class_of_line_data ha hell hcan⟩
  have hA : CanonicalRepresentative c.val B a := ⟨ha,hB,rfl,hcan⟩
  obtain ⟨-,u,hu,hcoeff⟩ := representative_unique c.property (chosenRepresentative c) hA
  refine ⟨c,?_⟩
  apply Subtype.ext
  change dualOf (chosenCoefficients c) (chosenNonzero c)=L.val
  rw [hL]
  exact (dual_eq_of_scalar ha (chosenNonzero c) u hcoeff.symm).symm

/-- A GENUINE native-projective equivalence, derived from actual divisors
and actual global canonical sections. No correspondence is an input. The
comparison of this intrinsic locus to ordinary square-contact lines is a
separate geometric theorem, not hidden in this equivalence. -/
def oddPicLineEquiv : OddPic ≃ OddNativeLine :=
  Equiv.ofBijective lineOf ⟨lineOf_injective,lineOf_surjective⟩

#print axioms lineOf_injective
#print axioms lineOf_surjective
#print axioms oddPicLineEquiv
end FourCorner.ThetaOddNativeLineEquiv
