import ElementaryPointBound
import Theorems.Thm_AlgebraicCurve_exists_monic_natCard_fixedPoints_restrictAlong_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_finite_setOf_deg_eq
import P2M.Sol.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places

set_option autoImplicit false

namespace AlgebraicCurve

/-- The sharp Hasse–Weil bound for every positive iterate of a supplied geometric
Frobenius. The polynomial and its trace formula are constructed, not assumed. -/
theorem finite_fixedPoints_and_abs_sub_pow_card_add_one_le
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [IsCurveOver k F₀] [IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    ∀ n : ℕ, 0 < n →
      (Function.fixedPoints (Place.restrictAlong φ hφi)^[n]).Finite ∧
      |(Nat.card (Function.fixedPoints (Place.restrictAlong φ hφi)^[n]) : ℝ) -
        ((Nat.card k : ℝ) ^ n + 1)| ≤
        2 * (genusFF K F : ℝ) * Real.sqrt (Nat.card k : ℝ) ^ n := by
  obtain ⟨P, hPm, hdeg, h0, hfix⟩ :=
    exists_monic_natCard_fixedPoints_restrictAlong_eq_of_constantFieldExtension
      k K F₀ F hfg hgen φ hφi hφ
  have hroot := norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
    k K F₀ F hfg hgen φ hφi hφ P hPm hdeg h0 (fun n hn => (hfix n hn).2)
  intro n hn
  exact ⟨(hfix n hn).1, HasseWeil.point_bound_of_root_data
    (Nat.card k) (genusFF K F)
    (Nat.card (Function.fixedPoints (Place.restrictAlong φ hφi)^[n])) n
    P hPm hdeg hroot (hfix n hn).2⟩

/-- The degree-one places are the rational points of the downstairs function
field. Both their count and the genus in this bound refer to that field. -/
theorem abs_card_degree_one_places_sub_card_add_one_le
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [IsCurveOver k F₀] [IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    |(Nat.card {v : Place k F₀ | v.deg = 1} : ℝ) - ((Nat.card k : ℝ) + 1)| ≤
      2 * (genusFF k F₀ : ℝ) * Real.sqrt (Nat.card k : ℝ) := by
  have hbound := finite_fixedPoints_and_abs_sub_pow_card_add_one_le
    k K F₀ F hfg hgen φ hφi hφ 1 (by decide)
  have hcount := finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
    k K F₀ F hfg hgen φ hφi hφ 1 (by decide)
  have hc : Nat.card (Function.fixedPoints (Place.restrictAlong φ hφi)^[1]) =
      Nat.card {v : Place k F₀ | v.deg = 1} := by
    simpa using hcount.2
  have hC := constantsAreBase_of_apply_algebraMap_eq_pow_card k K F₀ F hfg hgen φ hφ
  have hg := genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
    k K F₀ F hfg hgen φ hφ hC
  simpa only [hc, hg, pow_one] using hbound.2

/-- The degree-one-place bound together with finiteness of the counted set. -/
theorem finite_degree_one_places_and_abs_card_sub_card_add_one_le
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K]
    [Field F₀] [Field F] [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [IsCurveOver k F₀] [IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    {v : Place k F₀ | v.deg = 1}.Finite ∧
    |(Nat.card {v : Place k F₀ | v.deg = 1} : ℝ) - ((Nat.card k : ℝ) + 1)| ≤
      2 * (genusFF k F₀ : ℝ) * Real.sqrt (Nat.card k : ℝ) := by
  haveI : Algebra.EssFiniteType k F₀ := by
    obtain ⟨s, hs⟩ := hfg
    exact IntermediateField.fg_top_iff.mp ⟨s, hs⟩
  exact ⟨Place.finite_setOf_deg_eq k F₀ 1,
    abs_card_degree_one_places_sub_card_add_one_le k K F₀ F hfg hgen φ hφi hφ⟩

section FiniteField

open _root_.P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve.BombieriLower
open scoped P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve.BombieriLower

/-- Hasse–Weil for a finite-type function field over its finite full constant
field. The algebraic closure, geometric function field, and Frobenius are all
constructed within the proof. -/
theorem finite_degree_one_places_and_hasseWeil_bound
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (hC : ConstantsAreBase k F) :
    {v : Place k F | v.deg = 1}.Finite ∧
    |(Nat.card {v : Place k F | v.deg = 1} : ℝ) - ((Nat.card k : ℝ) + 1)| ≤
      2 * (genusFF k F : ℝ) * Real.sqrt (Nat.card k : ℝ) := by
  classical
  haveI : PerfectField k := PerfectField.ofFinite
  obtain ⟨x, hx, hfin, hsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  haveI := hfin
  haveI := hsep
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI := Fintype.ofFinite k
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨n, _, hcard⟩ := FiniteField.card k p
  have hq : Nat.card k = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hconst := hconst_of_constantsAreBase hC
  haveI : IsCurveOver (Kc k) (Fb k F) := isCurveOver_Fb (x := x) hx
  exact finite_degree_one_places_and_abs_card_sub_card_add_one_le
    k (Kc k) F (Fb k F) (hfg_F k F x) (hgen_Fb k F)
    (ψF (F := F) p (n : ℕ) hq hconst)
    (ψF_isIntegral p (n : ℕ) hq hconst)
    (ψF_algebraMap p (n : ℕ) hq hconst)

end FiniteField

end AlgebraicCurve
