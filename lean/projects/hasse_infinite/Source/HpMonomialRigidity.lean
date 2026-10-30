import HpDiagonalKernelRigidity

namespace FourCorner.HpMonomialRigidity
open HpDiagonalKernelRigidity
noncomputable section
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

/-- Carrying each of the five coordinate axes to an axis is already a
permutation with nonzero scalars, since the transformation is invertible. -/
theorem monomial_of_axes (L : V K ≃ₗ[K] V K)
    (haxes : ∀i : Fin 5,∃j,OnAxis j (L.symm (Pi.single i 1))) :
    ∃σ : Equiv.Perm (Fin 5),∃c : Fin 5 → K,(∀i,c i ≠ 0) ∧
      (∀i,L.symm (Pi.single i 1)=c i • Pi.single (σ i) 1) ∧
      ∀x i,(L x) i=x (σ i)/c i := by
  choose s hs using haxes
  let c : Fin 5 → K := fun i => L.symm (Pi.single i 1) (s i)
  have hcol (i : Fin 5) : L.symm (Pi.single i 1)=c i • Pi.single (s i) 1 :=
    (onAxis_iff _ _).mp (hs i)
  have hc (i : Fin 5) : c i ≠ 0 := by
    intro h
    have hh := congrArg L (hcol i)
    simpa [h] using hh
  have hi : Function.Injective s := by
    intro i j hij
    have he : (c i)⁻¹ • L.symm (Pi.single i 1)=(c j)⁻¹ • L.symm (Pi.single j 1) := by
      rw [hcol i,hcol j,hij]
      simp [smul_smul,hc]
    have hh : (c i)⁻¹ • Pi.single i (1 : K)=(c j)⁻¹ • Pi.single j 1 := by
      apply L.symm.injective
      simpa only [map_smul] using he
    have hl : LinearIndependent K (fun i : Fin 5 => Pi.single i (1 : K)) := by
      have heq : (fun i : Fin 5 => Pi.single i (1 : K))=⇑(Pi.basisFun K (Fin 5)) := by
        funext i
        exact (Pi.basisFun_apply K (Fin 5) i).symm
      rw [heq]
      exact (Pi.basisFun K (Fin 5)).linearIndependent
    exact hl.eq_of_smul_apply_eq_smul_apply _ _ i j (inv_ne_zero (hc i)) hh
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective s ⟨hi,Finite.surjective_of_injective hi⟩
  refine ⟨σ,c,hc,hcol,?_⟩
  intro x i
  have hx : x (σ i)=(L x) i*c i := by
    calc
      x (σ i)=(L.symm (L x)) (σ i) := by rw [L.symm_apply_apply]
      _=(∑j,(L x) j • L.symm (Pi.single j 1)) (σ i) := by
        conv_lhs => rw [pi_eq_sum_univ' (L x),map_sum]
        simp only [map_smul]
      _=(L x) i*c i := by
        simp only [hcol,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
        change (∑j,(L x) j*(c j*(if s i=s j then 1 else 0)))=(L x) i*c i
        simp [hi.eq_iff]
  exact (eq_div_iff (hc i)).mpr hx.symm

#print axioms monomial_of_axes
end
end FourCorner.HpMonomialRigidity
