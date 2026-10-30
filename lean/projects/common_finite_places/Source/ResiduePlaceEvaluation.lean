import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions

noncomputable section
open AlgebraicCurve
namespace FourCorner.ResiduePlaceEvaluation
variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- The actual residue evaluation at a degree-one/rational place over ANY
constant field, rather than a characteristic-zero-only evaluation. -/
def evaluate (w : Place k F) (hw : w.IsRational) : w.toValuationSubring →ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k w.ResidueField)
    ⟨(algebraMap k w.ResidueField).injective,hw⟩).symm.toAlgHom.comp
      (IsScalarTower.toAlgHom k w.toValuationSubring w.ResidueField)

theorem evaluate_constant (w : Place k F) (hw : w.IsRational) (a : k) :
    evaluate w hw (algebraMap k w.toValuationSubring a) = a := by
  simpa only [Algebra.algebraMap_self_apply] using (evaluate w hw).commutes a

theorem root_mem (w : Place k F) {a r : F} (ha : a ∈ w.toValuationSubring)
    (hr : r^2 = a) : r ∈ w.toValuationSubring := by
  have hi : IsIntegral w.toValuationSubring r := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hr]
    exact isIntegral_algebraMap (x := (⟨a,ha⟩ : w.toValuationSubring))
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact hy ▸ y.property

theorem inverse_mem (w : Place k F) (hw : w.IsRational)
    (a : w.toValuationSubring) (ha : evaluate w hw a ≠ 0) :
    (a : F)⁻¹ ∈ w.toValuationSubring := by
  have hres : IsLocalRing.residue w.toValuationSubring a ≠ 0 := by
    intro hz
    apply ha
    change (AlgEquiv.ofBijective (Algebra.ofId k w.ResidueField)
      ⟨(algebraMap k w.ResidueField).injective,hw⟩).symm
        (IsLocalRing.residue w.toValuationSubring a) = 0
    rw [hz,map_zero]
  obtain ⟨y,hy⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit a).mp hres).exists_left_inv
  have hyF : (y : F)*(a : F) = 1 := congrArg (fun z : w.toValuationSubring => (z : F)) hy
  have haF : (a : F) ≠ 0 := by intro h; rw [h,mul_zero] at hyF; exact zero_ne_one hyF
  have hyinv : (y : F) = (a : F)⁻¹ := by
    apply mul_right_cancel₀ haF
    rw [hyF,inv_mul_cancel₀ haF]
  exact hyinv ▸ y.property

/-- A pole's reciprocal is genuinely regular and has zero residue. This
retains all points over infinity for the subsequent local-chart construction. -/
theorem pole_inverse (w : Place k F) (hw : w.IsRational) {a : F}
    (ha : a ∉ w.toValuationSubring) :
    ∃ b : w.toValuationSubring, (b : F) = a⁻¹ ∧ evaluate w hw b = 0 := by
  have hi : a⁻¹ ∈ w.toValuationSubring := (w.toValuationSubring.mem_or_inv_mem a).resolve_left ha
  refine ⟨⟨a⁻¹,hi⟩,rfl,?_⟩
  by_contra h
  have hmem := inverse_mem w hw ⟨a⁻¹,hi⟩ h
  exact ha (by simpa only [inv_inv] using hmem)

end FourCorner.ResiduePlaceEvaluation
#print axioms FourCorner.ResiduePlaceEvaluation.evaluate_constant
#print axioms FourCorner.ResiduePlaceEvaluation.pole_inverse
