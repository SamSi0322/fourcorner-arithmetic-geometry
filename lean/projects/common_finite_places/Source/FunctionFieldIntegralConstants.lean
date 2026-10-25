import geometry.RatFuncFiniteExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable

noncomputable section
open AlgebraicCurve
namespace FourCorner.FunctionFieldIntegralConstants
variable (K F : Type*) [Field K] [PerfectField K] [Field F]
  [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
set_option maxHeartbeats 1000000

/-- Everywhere-regular functions in this actual one-variable field are
integral over its constants, in positive characteristic as well. -/
theorem lSpace_zero_integral {x : F} (hx : x ∈ LSpace (0 : Divisor K F)) :
    IsIntegral K x := by
  obtain ⟨s,hs,hfd,hsep⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField
    (FourCorner.RatFuncFiniteExtension.transcendental_X K F)
    (FourCorner.RatFuncFiniteExtension.finiteDimensional_adjoin_X K F)
  letI := hfd
  letI := hsep
  by_contra hnot
  have hxIC : x ∉ (integralClosure K F).toSubring := fun h => hnot h
  obtain ⟨V,hICV,hxV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure K F).toSubring) hxIC
  have hKV : ∀ a : K, (RingHom.id F) (algebraMap K F a) ∈ V := fun a =>
    hICV (Subalgebra.algebraMap_mem (integralClosure K F) a)
  obtain ⟨v,hv⟩ := Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
    (K := K) (F := F) (F' := F) s (RingHom.id F) V hKV ⟨x,hxV⟩
  have hxmem : x ∈ v.toValuationSubring := by
    apply v.mem_iff_adicValuation_le_one.mpr
    simpa only [Finsupp.zero_apply,WithZero.exp_zero] using (mem_lSpace_iff.mp hx v)
  rw [hv] at hxmem
  exact hxV hxmem

end FourCorner.FunctionFieldIntegralConstants
#print axioms FourCorner.FunctionFieldIntegralConstants.lSpace_zero_integral
