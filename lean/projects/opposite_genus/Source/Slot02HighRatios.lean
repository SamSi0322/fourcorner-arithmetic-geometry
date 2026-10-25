import Slot02OppositeProjective
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace Slot02HighProjSpace
section PnSetup
variable (R : Type u) [CommRing R] (n : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
def grad0Equiv : R ≃+* (𝒜 0) where
  toFun r := ⟨C r, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ r)⟩
  invFun p := MvPolynomial.constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    ext : 1
    have hp : p.1.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp p.2
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [MvPolynomial.constantCoeff]
    · rw [MvPolynomial.coeff_C, if_neg (Ne.symm hd)]
      by_contra h
      refine hd (Finsupp.ext fun i => ?_)

      have hdeg : (Finsupp.weight (1 : Fin (n + 1) → ℕ)) d = 0 := hp (fun h0 => h h0.symm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Finsupp.sum] at hdeg
      by_cases hi : i ∈ d.support
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hdeg i hi
      · exact Finsupp.notMem_support_iff.mp hi
  map_mul' a b := by ext : 1; simp
  map_add' a b := by ext : 1; simp

end PnSetup
section Setup

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem X_mem_one (j : Fin (n + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R j)

instance algebraAway (i : Fin (n + 1)) :
    Algebra R (Away 𝒜 (MvPolynomial.X i)) :=
  ((HomogeneousLocalization.fromZeroRingHom 𝒜 _).comp
    (grad0Equiv R n).toRingHom).toAlgebra

def ratio (i k : Fin (n + 1)) : Away 𝒜 (MvPolynomial.X i) :=
  Away.mk 𝒜 (X_mem_one R n i) 1 (MvPolynomial.X k)
    (by simpa using X_mem_one R n k)

theorem ratio_self (i : Fin (n + 1)) :
    ratio R n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio, Away.val_mk, HomogeneousLocalization.val_one,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem val_algebraMap (i : Fin (n + 1)) (r : R) :
    (algebraMap R (Away 𝒜 (MvPolynomial.X i)) r).val
      = algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.C r) := by
  rfl

end Setup

section AdjoinRatio

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem awayMk_monomial (i : Fin (n + 1)) (d : ℕ)
    (e : Fin (n + 1) →₀ ℕ) (hd : e.degree = d) (r : R)
    (hm : MvPolynomial.monomial e r ∈ 𝒜 (d • 1)) :
    Away.mk 𝒜 (X_mem_one R n i) d (MvPolynomial.monomial e r) hm
      = algebraMap R _ r * ∏ j, (ratio R n i j) ^ (e j) := by
  have hdsum : ∑ j, e j = d := by
    rw [← hd, Finsupp.degree]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun j _ hj => Finsupp.notMem_support_iff.mp hj)).symm
  apply HomogeneousLocalization.val_injective
  have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
      = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
  rw [hval, map_mul, map_prod]
  simp only [map_pow, ratio, ← hval, Away.val_mk,
    val_algebraMap, Localization.mk_pow,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_prod, Localization.mk_mul]
  congr 1
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
  · refine Subtype.ext ?_
    push_cast
    simp only [Finset.prod_pow_eq_pow_sum, pow_one, one_mul, hdsum]

theorem adjoin_range_ratio (i : Fin (n + 1)) :
    Algebra.adjoin R (Set.range (ratio R n i)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem_one R n i) z
  have ha' : a.IsHomogeneous d := (mem_homogeneousSubmodule d a).mp (by simpa using ha)

  have hdeg : ∀ e ∈ a.support, (e : Fin (n + 1) →₀ ℕ).degree = d := fun e he => by
    rw [Finsupp.degree_eq_weight_one]; exact ha' (MvPolynomial.mem_support_iff.mp he)
  have hsum : Away.mk 𝒜 (X_mem_one R n i) d a ha
      = ∑ e ∈ a.support.attach,
          Away.mk 𝒜 (X_mem_one R n i) d
            (MvPolynomial.monomial e.1 (a.coeff e.1))
            ((mem_homogeneousSubmodule _ _).mpr
              (isHomogeneous_monomial _
                (by simp only [smul_eq_mul, mul_one]; exact hdeg e.1 e.2))) := by
    apply HomogeneousLocalization.val_injective
    have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
        = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
    rw [hval, map_sum]
    simp only [← hval, Away.val_mk]
    rw [Finset.sum_attach a.support
      (fun e => Localization.mk (monomial e (a.coeff e))
        (⟨(X i)^d, Away.val_mk._proof_1 d⟩ :
          Submonoid.powers (X i : MvPolynomial (Fin (n+1)) R))),
      ← Localization.mk_sum]
    congr 1
    exact MvPolynomial.as_sum a
  rw [hsum]
  refine Subalgebra.sum_mem _ fun e _ => ?_
  rw [awayMk_monomial R n i d e.1 (hdeg e.1 e.2) (a.coeff e.1)]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.prod_mem _ fun j _ =>
      Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _)

end AdjoinRatio

end Slot02HighProjSpace
end AlgebraicGeometry
end
