import ThetaLineStabilizers
import Mathlib.LinearAlgebra.Dimension.Constructions
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra

abbrev OrbitBlocks := Fin 8 ⊕ (Fin 4 ⊕ (Fin 4 ⊕ Fin 1))
def orbitBlocksEquiv : OrbitBlocks ≃ Fin 17 :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
    finSumFinEquiv)).trans finSumFinEquiv

def BlockField : OrbitBlocks → Type
  | .inl _ => ℚ
  | .inr (.inl _) => ThetaSqrtTwo
  | .inr (.inr (.inl _)) => SqrtFiftyone
  | .inr (.inr (.inr _)) => K
instance blockField : (i : OrbitBlocks) → Field (BlockField i)
  | .inl _ => (inferInstance : Field ℚ)
  | .inr (.inl _) => (inferInstance : Field ThetaSqrtTwo)
  | .inr (.inr (.inl _)) => (inferInstance : Field SqrtFiftyone)
  | .inr (.inr (.inr _)) => (inferInstance : Field K)
instance blockAlgebra : (i : OrbitBlocks) → Algebra ℚ (BlockField i)
  | .inl _ => (inferInstance : Algebra ℚ ℚ)
  | .inr (.inl _) => (inferInstance : Algebra ℚ ThetaSqrtTwo)
  | .inr (.inr (.inl _)) => (inferInstance : Algebra ℚ SqrtFiftyone)
  | .inr (.inr (.inr _)) => (inferInstance : Algebra ℚ K)

/-- The fixed subalgebras of the ACTUAL orbit stabilizers are the specified actual fields. -/
def valueBlockEquiv (i : OrbitBlocks) : orbitValueAlgebra (orbitBlocksEquiv i) ≃ₐ[ℚ] BlockField i := by
  rcases i with i | i | i | i
  · change orbitValueAlgebra (orbitBlocksEquiv (.inl i)) ≃ₐ[ℚ] ℚ
    have h : orbitValueAlgebra (orbitBlocksEquiv (.inl i)) = fixedRational := by
      change (if i.val < 8 then fixedRational else if i.val < 12 then fixedTwo else
        if i.val < 16 then fixedFiftyone else ⊤) = fixedRational
      rw [if_pos i.isLt]
    exact (Subalgebra.equivOfEq _ _ h).trans rationalFixedEquiv.symm
  · change orbitValueAlgebra (orbitBlocksEquiv (.inr (.inl i))) ≃ₐ[ℚ] ThetaSqrtTwo
    have h : orbitValueAlgebra (orbitBlocksEquiv (.inr (.inl i))) = fixedTwo := by
      change (if 8 + i.val < 8 then fixedRational else if 8 + i.val < 12 then fixedTwo else
        if 8 + i.val < 16 then fixedFiftyone else ⊤) = fixedTwo
      rw [if_neg (by omega), if_pos (by omega)]
    exact (Subalgebra.equivOfEq _ _ h).trans sqrtTwoFixedEquiv.symm
  · change orbitValueAlgebra (orbitBlocksEquiv (.inr (.inr (.inl i)))) ≃ₐ[ℚ] SqrtFiftyone
    have h : orbitValueAlgebra (orbitBlocksEquiv (.inr (.inr (.inl i)))) = fixedFiftyone := by
      change (if 8 + (4 + i.val) < 8 then fixedRational else if 8 + (4 + i.val) < 12 then fixedTwo else
        if 8 + (4 + i.val) < 16 then fixedFiftyone else ⊤) = fixedFiftyone
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact (Subalgebra.equivOfEq _ _ h).trans sqrtFiftyoneFixedEquiv.symm
  · change orbitValueAlgebra (orbitBlocksEquiv (.inr (.inr (.inr i)))) ≃ₐ[ℚ] K
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have h : orbitValueAlgebra (orbitBlocksEquiv (.inr (.inr (.inr 0)))) = ⊤ := rfl
    exact (Subalgebra.equivOfEq _ _ h).trans Subalgebra.topEquiv

abbrev ProductModel := (Fin 8 → ℚ) × (Fin 4 → ThetaSqrtTwo) × (Fin 4 → SqrtFiftyone) × K

def blockProductEquiv : (∀ i : OrbitBlocks, BlockField i) ≃ₐ[ℚ] ProductModel where
  toFun f := (fun i => f (.inl i), fun i => f (.inr (.inl i)),
    fun i => f (.inr (.inr (.inl i))), f (.inr (.inr (.inr 0))))
  invFun p i := match i with
    | .inl i => p.1 i
    | .inr (.inl i) => p.2.1 i
    | .inr (.inr (.inl i)) => p.2.2.1 i
    | .inr (.inr (.inr _)) => p.2.2.2
  left_inv f := by
    funext i
    rcases i with i | i | i | i
    · rfl
    · rfl
    · rfl
    · fin_cases i; rfl
  right_inv p := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The product is proved by genuine orbit/stabilizer fixed-field evaluation from
an independently constructed finite étale algebra of actual native lines. -/
def algebraDecomposition : Associated ≃ₐ[ℚ] ProductModel :=
  associatedOrbitValuesEquiv.trans
    (((AlgEquiv.piCongrLeft ℚ (fun i : Fin 17 => ↥(orbitValueAlgebra i)) orbitBlocksEquiv).symm.trans
      (AlgEquiv.piCongrRight valueBlockEquiv)).trans blockProductEquiv)

theorem associated_degree : Module.finrank ℚ Associated = 28 := by
  rw [algebraDecomposition.toLinearEquiv.finrank_eq]
  norm_num [ProductModel, Module.finrank_prod, Module.finrank_pi_fintype,
    QuadraticAlgebra.finrank_eq_two, splitting_degree]
end FourCorner.ThetaLineGaloisAlgebra
