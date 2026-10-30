import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace FourCorner.RiemannRochWithGenusFF
open AlgebraicCurve

/-- Genuine all-divisor RR existence with the proved genusFF identification,
for the actual given function field; no RR equation is assumed. -/
theorem exists_rr {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ Kc : Divisor K F, ∀ D : Divisor K F,
      (ell D:ℤ)-ell (Kc-D)=Divisor.degree D+1-genusFF K F := by
  obtain ⟨Kc,g,hRR⟩ := P2MW.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch.solution K F
  obtain ⟨t,ht,hfd,hsep⟩ := IsCurveOver.exists_separating_transcendental (K:=K) (F:=F)
  letI := hfd
  have hC := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hg := eq_genusFF_of_forall_ell_sub_ell_eq hC hRR
  subst g
  exact ⟨Kc,hRR⟩

#print axioms exists_rr
end FourCorner.RiemannRochWithGenusFF
