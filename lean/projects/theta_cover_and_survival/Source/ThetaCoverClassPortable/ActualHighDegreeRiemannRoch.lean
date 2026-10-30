import ThetaCoverClassPortable.RiemannRochWithGenusFF
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg

noncomputable section
set_option autoImplicit false
open AlgebraicCurve
namespace FourCorner.ActualPicardProperties

/-- The large-degree numerical consequence of genuine all-divisor RR.
No cohomological vanishing is supplied as a premise. -/
theorem high_degree_ell_of_rr
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
    [Algebra.EssFiniteType k F]
    (Kc : Divisor k F) (g : ℕ)
    (hRR : ∀ D : Divisor k F, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - g)
    (D : Divisor k F) (hr : 2 * (g : ℤ) ≤ Divisor.degree D + 1) :
    (ell D : ℤ) = Divisor.degree D + 1 - g := by
  obtain ⟨t,ht,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=k) (F:=F)
  letI := hfd
  have hC := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hz : ell (0 : Divisor k F) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  have h0 := hRR 0
  have hK := hRR Kc
  simp only [sub_zero,map_zero,hz,Nat.cast_one,sub_self] at h0 hK
  have hdeg : Divisor.degree Kc = 2 * (g : ℤ) - 2 := by linarith
  have hneg : Divisor.degree (Kc-D) < 0 := by rw [map_sub,hdeg]; linarith
  have hv : ell (Kc-D) = 0 := ell_eq_zero_of_degree_neg hneg
  simpa only [hv,Nat.cast_zero,sub_zero] using hRR D

#print axioms high_degree_ell_of_rr
end FourCorner.ActualPicardProperties
