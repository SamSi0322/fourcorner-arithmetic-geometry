import CriticalBoundaryPlaceClassification
import CriticalBoundaryCardinality

noncomputable section
namespace FourCorner.CriticalBoundaryEight
open AlgebraicCurve CriticalBoundaryTower CriticalBoundaryFibres CriticalBoundaryClassification
open CriticalBoundaryResidues CriticalElliptic23 ResiduePlaceEvaluation
variable {k : Type*} [Field k]
set_option maxHeartbeats 2000000

/-- The original ordering is a,b,c, corresponding to Fin3 coordinates0,1,2. -/
def tripleEquiv : (Bool×(Bool×Bool)) ≃ (Fin 3 → Bool) where
  toFun e := ![e.1,e.2.1,e.2.2]
  invFun e := (e 0,e 1,e 2)
  left_inv e := by rcases e with ⟨x,y,z⟩;rfl
  right_inv e := by funext j;fin_cases j <;> rfl

/-- Every rational boundary place of the original critical biquadratic field
corresponds to exactly one of its eight original sign triples. Both actual
quadratic place fibres, and their residue evaluations, are constructed. -/
def boundaryEquiv (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Boundary i ≃ (Fin 3 → Bool) :=
  (boundarySigmaEquiv i hi h2).trans
    ((Equiv.sigmaEquivProdOfEquiv (lineFibreEquiv i hi h2)).trans tripleEquiv)

theorem boundaryEquiv_apply (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (w : Boundary i) :
    boundaryEquiv i hi h2 w=
      ![firstLabel i hi h2 w,
        (lineFibreEquiv i hi h2 (firstLabel i hi h2 w)
          ⟨w.val,boundary_line i hi h2 w,w.property.1⟩).1,
        (lineFibreEquiv i hi h2 (firstLabel i hi h2 w)
          ⟨w.val,boundary_line i hi h2 w,w.property.1⟩).2] := by
  unfold boundaryEquiv
  rw [Equiv.trans_apply,boundarySigmaEquiv_apply]
  rfl

/-- The three signs are the genuine evaluations of a,b,c at the SAME
original rational boundary place. -/
theorem boundaryEquiv_evaluations (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (w : Boundary i) :
    evaluate w.val w.property.1 (A i hi h2 w.val w.property.2)=sign (boundaryEquiv i hi h2 w 0) ∧
    evaluate w.val w.property.1 (B i hi h2 w.val w.property.2)=sign (boundaryEquiv i hi h2 w 1) ∧
    evaluate w.val w.property.1 (C i hi h2 w.val w.property.2)=sign (boundaryEquiv i hi h2 w 2) := by
  let v : FullFibre i (firstLabel i hi h2 w) := ⟨w.val,boundary_line i hi h2 w,w.property.1⟩
  have h := lineFibre_coordinates i hi h2 (firstLabel i hi h2 w) v
    (B i hi h2 w.val w.property.2) (C i hi h2 w.val w.property.2) rfl rfl
  rw [boundaryEquiv_apply]
  change evaluate w.val w.property.1 (A i hi h2 w.val w.property.2)=sign (firstLabel i hi h2 w) ∧
    evaluate w.val w.property.1 (B i hi h2 w.val w.property.2)=sign (lineFibreEquiv i hi h2 _ v).1 ∧
    evaluate w.val w.property.1 (C i hi h2 w.val w.property.2)=sign (lineFibreEquiv i hi h2 _ v).2
  exact ⟨(firstLabel_value i hi h2 w).symm,h.1.symm,h.2.symm⟩

/-- Inverse signs construct actual boundary places, retaining all three
coordinate evaluations rather than merely asserting their cardinality. -/
theorem boundaryEquiv_symm_evaluations (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (e : Fin 3 → Bool) :
    let w := (boundaryEquiv i hi h2).symm e
    evaluate w.val w.property.1 (A i hi h2 w.val w.property.2)=sign (e 0) ∧
    evaluate w.val w.property.1 (B i hi h2 w.val w.property.2)=sign (e 1) ∧
    evaluate w.val w.property.1 (C i hi h2 w.val w.property.2)=sign (e 2) := by
  have h := boundaryEquiv_evaluations i hi h2 ((boundaryEquiv i hi h2).symm e)
  rwa [Equiv.apply_symm_apply] at h

/-- The boundary contains eight ACTUAL rational places over arbitrary
constant fields containing i, with characteristic different from two. -/
theorem boundary_card (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) : Nat.card (Boundary i)=8 := by
  rw [Nat.card_congr (boundaryEquiv i hi h2)]
  norm_num [Nat.card_eq_fintype_card]

/-- The labels also give exactly the eight original signed projective
points. This uses their explicit coordinate construction, not an assumed
closed-point/place equivalence over finite constants. -/
def signedProjectiveEquiv (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Boundary i ≃ Set.range (signedPoint (k:=k)) :=
  (boundaryEquiv i hi h2).trans (Equiv.ofInjective _ (signedPoint_injective h2))

/-- The same correspondence with the eight explicitly constructed ORIGINAL
Scheme points, using only their proved injection and their literal signs.
No identification of all finite-field closed points with places is used. -/
def signedSchemeEquiv (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Boundary i ≃ Set.range (CriticalSignPoints.point i) :=
  (boundaryEquiv i hi h2).trans
    (Equiv.ofInjective _ (CriticalBoundaryCardinality.point_injective i h2))

#print axioms signedSchemeEquiv

#print axioms boundaryEquiv
#print axioms boundaryEquiv_evaluations
#print axioms boundaryEquiv_symm_evaluations
#print axioms boundary_card
#print axioms signedProjectiveEquiv
end FourCorner.CriticalBoundaryEight
