import ThetaDNativeSections
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver

namespace FourCorner.ThetaRegularFunctionDifferential
open AlgebraicCurve
noncomputable section
variable {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]
local instance : ∀v : Place K F,v.DCoordGenerates := dCoordGenerates_of_isCurveOver
attribute [local instance] Classical.propDecidable

def coefficient (w : Place K F) : Ω[F⁄K] →ₗ[F] F where
  toFun := w.differentialCoeff
  map_add' a b := w.differentialCoeff_unique (by rw [add_smul,w.differentialCoeff_smul_dCoord,w.differentialCoeff_smul_dCoord])
  map_smul' c a := w.differentialCoeff_smul c a

/-- The differential of ANY regular local function is regular at the
actual place. This is derived, not assumed as a local-parameter condition. -/
theorem coefficient_D_mem (w : Place K F) (f : F) (hf : f∈w.toValuationSubring) :
    coefficient w (KaehlerDifferential.D K F f)∈w.toValuationSubring := by
  by_cases h0 : f=0
  · simp [h0,coefficient]
  let A := w.toValuationSubring
  let π : A := (IsDiscreteValuationRing.exists_irreducible A).choose
  have hπ : Irreducible π := (IsDiscreteValuationRing.exists_irreducible A).choose_spec
  obtain ⟨n,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x:=(⟨f,hf⟩:A)) (by intro h;exact h0 (congrArg (fun a : A => (a:F)) h)) hπ
  have hfc : f=((u:A):F)*(π:F)^n := by
    have hh:=congrArg (fun a : A => (a:F)) hu
    exact hh
  have hun : ((u:A):F) ≠ 0 := by
    intro h
    exact Units.ne_zero u (Subtype.ext h)
  have hou : w.ord ((u:A):F)=0 := by
    have hh := w.ord_unit_smul_zpow u hπ (0:ℤ)
    simpa using hh
  have hcu : coefficient w (KaehlerDifferential.D K F ((u:A):F))∈A := by
    have hh := localUnitDerivativeRegular_of_isCurveOver w ((u:A):F) hun hou
    rcases hh with hz | hh
    · change w.differentialCoeff _∈A
      rw [hz]
      exact zero_mem _
    · by_cases hz : w.differentialCoeff (KaehlerDifferential.D K F ((u:A):F))=0
      · change w.differentialCoeff _∈A
        rw [hz]
        exact zero_mem _
      · exact w.mem_of_ord_nonneg hz hh
  have hcp : coefficient w (KaehlerDifferential.D K F (π:F))∈A := by
    have hh : coefficient w (KaehlerDifferential.D K F (π:F))=1 := by
      change w.differentialCoeff _=1
      have hsame : w.dCoord=KaehlerDifferential.D K F (π:F) := rfl
      rw [←hsame,w.differentialCoeff_dCoord]
    rw [hh]
    exact one_mem _
  rw [hfc,Derivation.leibniz,Derivation.leibniz_pow,map_add]
  simp only [map_smul,map_nsmul,smul_eq_mul,nsmul_eq_mul]
  have hnat : (n:F)∈A := by simpa only [map_natCast] using w.algebraMap_mem' (n:K)
  change _ ∈ A.toSubring
  simpa only [add_comm,mul_assoc] using A.toSubring.add_mem
    (A.toSubring.mul_mem (A.toSubring.pow_mem π.property n) hcu)
    (A.toSubring.mul_mem (u:A).property (A.toSubring.mul_mem hnat (A.toSubring.mul_mem (A.toSubring.pow_mem π.property (n-1)) hcp)))

#print axioms coefficient_D_mem
end
end FourCorner.ThetaRegularFunctionDifferential
