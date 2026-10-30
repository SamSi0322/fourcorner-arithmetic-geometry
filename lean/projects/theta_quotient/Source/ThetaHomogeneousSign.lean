import ThetaInvolution
noncomputable section
namespace FourCorner.ThetaHomogeneousSign
open MvPolynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
lemma eval₂_neg {A : Type*} [CommRing A] (f : ℚ →+* A) (g : Fin 5 → A)
    {p : MvPolynomial (Fin 5) ℚ} {d : ℕ} (hp : p.IsHomogeneous d) :
    eval₂ f (fun i=> -g i) p=(-1:A)^d*eval₂ f g p := by
  rw [←p.support_sum_monomial_coeff,eval₂_sum,eval₂_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd:=hp.degree_eq_sum_deg_support hm
  simp only [eval₂_monomial,Finsupp.prod]
  have hpow (i : Fin 5) : (-g i)^(m i)=(-1:A)^(m i)*(g i)^(m i) := by
    rw [←mul_pow]
    congr 1
    ring
  simp only [hpow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,←hd]
  ring
end FourCorner.ThetaHomogeneousSign
#print axioms FourCorner.ThetaHomogeneousSign.eval₂_neg
