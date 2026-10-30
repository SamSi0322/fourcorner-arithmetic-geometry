import CriticalBoundaryFibres
import RationalLinePlaceImage

noncomputable section
namespace FourCorner.CriticalBoundaryClassification
open AlgebraicCurve AlgebraicCurve.RationalFunctionField Polynomial
open CriticalBoundaryTower CriticalBoundaryFibres CriticalBoundaryResidues CriticalRadicalField
open CriticalElliptic23 CriticalSignPoints ResiduePlaceEvaluation RationalPlaceFibreHom RationalPlaceTower RationalLineEvaluation
variable {k : Type*} [Field k]
set_option maxHeartbeats 2000000

abbrev Boundary (i : k) := {w : Place k (Full i) // w.IsRational ∧ 0<w.ord (shift i)}

def valueA (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (w : Boundary i) : k :=
  evaluate w.val w.property.1 (A i hi h2 w.val w.property.2)

def firstLabel (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (w : Boundary i) : Bool :=
  (signRoots h2 1 rfl).symm ⟨valueA i hi h2 w,
    (residue_squares i hi h2 w.val w.property.1 w.property.2).1⟩

theorem firstLabel_value (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (w : Boundary i) :
    sign (firstLabel i hi h2 w)=valueA i hi h2 w := signRoots_inverse _ _ _ _

/-- Every actual rational boundary place lies over exactly one of the two
original finite line places, without an algebraically closed hypothesis. -/
theorem boundary_line (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (w : Boundary i) :
    w.val.restrict (RatFunc k)=linePlace (firstLabel i hi h2 w) := by
  letI : NeZero (2:k) := ⟨h2⟩
  letI := CriticalActualRamification.separable i h2
  have h := RationalLinePlaceImage.finite_image (k:=k) (E:=Full i) w.val w.property.1
    (A i hi h2 w.val w.property.2).property
  change w.val.restrict (RatFunc k)=placeOfPoint k (valueA i hi h2 w) at h
  rw [←firstLabel_value i hi h2 w] at h
  exact h

/-- The original a-coordinate evaluates to the actual line value for every
rational place in that fibre. -/
theorem parameter_value (i : k) (h2 : (2:k)≠0) (e : Bool) (w : FullFibre i e)
    (R : w.val.toValuationSubring) (hR : (R:Full i)=a k i) :
    evaluate w.val w.property.2 R=sign e := by
  letI := CriticalActualRamification.separable i h2
  have he : R=baseInclusion (linePlace e) w.val w.property.1 (xAt (sign e)) := by
    apply Subtype.ext
    rw [baseInclusion_coe]
    exact hR
  rw [he,evaluate_baseInclusion (linePlace e) (rational (sign e)),evaluate_xAt]

/-- Every rational place above either line sign is an actual boundary place. -/
theorem line_boundary (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Bool)
    (w : FullFibre i e) : 0<w.val.ord (shift i) := by
  letI := CriticalActualRamification.separable i h2
  let t := polynomialAt (sign (k:=k) e) (X^2-Polynomial.C 1)
  let T := baseInclusion (linePlace e) w.val w.property.1 t
  have ht : (T:Full i)=shift i := by
    dsimp only [T]
    rw [baseInclusion_coe]
    dsimp only [t]
    rw [polynomialAt_coe]
    simp [shift,a]
  have he : evaluate w.val w.property.2 T=0 := by
    dsimp only [T]
    rw [evaluate_baseInclusion (linePlace e) (rational (sign e))]
    dsimp only [t]
    rw [evaluate_polynomialAt]
    simp [sign_sq]
  have hn : (T:Full i)≠0 := by rw [ht];exact (CriticalBadUnits.ordered_nonzero i hi h2).2.2.2
  have ho := (ResidueValuationFacts.evaluate_zero_iff_ord_pos w.val w.property.2 T hn).mp he
  rwa [ht] at ho

/-- Construct the actual boundary place from either actual line fibre. -/
def boundaryOfFibre (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (w : Σ e : Bool,FullFibre i e) : Boundary i :=
  ⟨w.2.val,w.2.property.2,line_boundary i hi h2 w.1 w.2⟩

theorem boundaryOfFibre_injective (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Function.Injective (boundaryOfFibre i hi h2) := by
  rintro ⟨e,w⟩ ⟨f,z⟩ h
  have hwz : w.val=z.val := congrArg Subtype.val h
  have hl := congrArg (fun x : Place k (Full i) => x.restrict (RatFunc k)) hwz
  rw [w.property.1,z.property.1] at hl
  have hef : e=f := sign_injective h2 (placeOfPoint_injective k hl)
  subst f
  have hw : w=z := Subtype.ext hwz
  subst z
  rfl

theorem boundaryOfFibre_surjective (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Function.Surjective (boundaryOfFibre i hi h2) := by
  intro w
  refine ⟨⟨firstLabel i hi h2 w,⟨w.val,boundary_line i hi h2 w,w.property.1⟩⟩,?_⟩
  exact Subtype.ext rfl

/-- The entire actual rational boundary is the disjoint union of the two
actual rational line fibres; it is not assigned a finite sign list. -/
def boundarySigmaEquiv (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Boundary i ≃ Σ e : Bool,FullFibre i e :=
  (Equiv.ofBijective (boundaryOfFibre i hi h2)
    ⟨boundaryOfFibre_injective i hi h2,boundaryOfFibre_surjective i hi h2⟩).symm

theorem boundarySigmaEquiv_apply (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (w : Boundary i) :
    boundarySigmaEquiv i hi h2 w=
      ⟨firstLabel i hi h2 w,⟨w.val,boundary_line i hi h2 w,w.property.1⟩⟩ := by
  apply (boundarySigmaEquiv i hi h2).symm.injective
  rw [Equiv.symm_apply_apply]
  exact Subtype.ext rfl

#print axioms boundary_line
#print axioms line_boundary
#print axioms boundarySigmaEquiv
end FourCorner.CriticalBoundaryClassification
