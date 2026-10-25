import CommonActualBoundary
import CommonRootExclusion
noncomputable section
namespace FourCorner.CommonLiteralField
open AlgebraicCurve CommonRationalPlace
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- Actual rational places, including places over every branch value and infinity,
produce the ordered affine common-root source after the boundary exclusions. -/
def rationalPlaceSource07 (t : ℚ) (ht : 1 < t)
    (w : Place ℚ (field ℚ t)) (hw : w.IsRational) : CommonRootSource ℚ t := by
  let A := w.toValuationSubring
  let f := rationalEval w hw
  have he := ell_regular_at_rational_place t ht w hw
  let E : A := ⟨ell ℚ t,he⟩
  have hav := rational_place_avoids_finite_boundary t ht w hw
  have hav' : f E ≠ 0 ∧ f E ≠ t-1 ∧ f E ≠ t+1 ∧
      f E ≠ -(t-1) ∧ f E ≠ -(t+1) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hav
  have hinv := inv_mem_of_eval_ne_zero w hw E hav'.1
  have hp : root ℚ t 0 ∈ A := root_mem w
    (A.add_mem _ _ he (w.algebraMap_mem' (t+1)))
    (by simpa only [eq_ratCast] using sqP ℚ t)
  have hc : root ℚ t 1 ∈ A := root_mem w
    (A.sub_mem he (w.algebraMap_mem' (t-1)))
    (by simpa only [eq_ratCast] using sqC ℚ t)
  have hm : root ℚ t 2 ∈ A := root_mem w
    (by simpa only [div_eq_mul_inv] using A.mul_mem _ _
          (A.mul_mem _ _ (w.algebraMap_mem' (t-1))
            (A.sub_mem (w.algebraMap_mem' (t+1)) he)) hinv)
    (by simpa only [eq_ratCast,div_eq_mul_inv,E] using sqM ℚ t)
  have hb : root ℚ t 3 ∈ A := root_mem w
    (by simpa only [div_eq_mul_inv] using A.mul_mem _ _
          (A.mul_mem _ _ (w.algebraMap_mem' (t+1))
            (A.add_mem _ _ he (w.algebraMap_mem' (t-1)))) hinv)
    (by simpa only [eq_ratCast,div_eq_mul_inv,E] using sqB ℚ t)
  let P : A := ⟨root ℚ t 0,hp⟩
  let C : A := ⟨root ℚ t 1,hc⟩
  let M : A := ⟨root ℚ t 2,hm⟩
  let B : A := ⟨root ℚ t 3,hb⟩
  have hP : P^2 = E + algebraMap ℚ A (t+1) := by
    apply Subtype.ext
    change root ℚ t 0 ^ 2 = ell ℚ t + algebraMap ℚ (field ℚ t) (t+1)
    simpa only [eq_ratCast] using sqP ℚ t
  have hC : C^2 = E - algebraMap ℚ A (t-1) := by
    apply Subtype.ext
    change root ℚ t 1 ^ 2 = ell ℚ t - algebraMap ℚ (field ℚ t) (t-1)
    simpa only [eq_ratCast] using sqC ℚ t
  have hM : E*M^2 = algebraMap ℚ A (t-1)*(algebraMap ℚ A (t+1)-E) := by
    apply Subtype.ext
    change ell ℚ t * root ℚ t 2 ^ 2 = algebraMap ℚ (field ℚ t) (t-1)*(algebraMap ℚ (field ℚ t) (t+1)-ell ℚ t)
    rw [sqM]; simp only [eq_ratCast]; field_simp [ell_ne_zero]
  have hB : E*B^2 = algebraMap ℚ A (t+1)*(E+algebraMap ℚ A (t-1)) := by
    apply Subtype.ext
    change ell ℚ t * root ℚ t 3 ^ 2 = algebraMap ℚ (field ℚ t) (t+1)*(ell ℚ t+algebraMap ℚ (field ℚ t) (t-1))
    rw [sqB]; simp only [eq_ratCast]; field_simp [ell_ne_zero]
  have hP' := congrArg f hP
  have hC' := congrArg f hC
  have hM' := congrArg f hM
  have hB' := congrArg f hB
  have hf (q : ℚ) : f (algebraMap ℚ A q) = q := f.commutes q
  simp only [map_pow,map_add,map_sub,map_mul] at hP' hC' hM' hB'
  simp only [hf] at hP' hC' hM' hB'
  refine { ell := f E
           P := f P
           C := f C
           M := f M
           B := f B
           t_ne_zero := by linarith
           t_ne_one := by linarith
           t_ne_neg_one := by linarith
           ell_ne_zero := hav'.1
           P_ne_zero := ?_
           C_ne_zero := ?_
           M_ne_zero := ?_
           B_ne_zero := ?_
           sqP := hP'
           sqC := hC'
           sqM := ?_
           sqB := ?_ }
  · intro hz; apply hav'.2.2.2.2; rw [hz] at hP'; norm_num at hP'; linarith
  · intro hz; apply hav'.2.1; rw [hz] at hC'; norm_num at hC'; linarith
  · intro hz; apply hav'.2.2.1
    rw [hz] at hM'; norm_num only [zero_pow, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hM'
    have : t-1 ≠ 0 := by linarith
    rcases mul_eq_zero.mp hM'.symm with hh | hh
    · exact False.elim (this hh)
    · linarith
  · intro hz; apply hav'.2.2.2.1
    rw [hz] at hB'; norm_num only [zero_pow, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hB'
    have : t+1 ≠ 0 := by linarith
    rcases mul_eq_zero.mp hB'.symm with hh | hh
    · exact False.elim (this hh)
    · linarith
  · apply (eq_div_iff hav'.1).mpr; nlinarith [hM']
  · apply (eq_div_iff hav'.1).mpr; nlinarith [hB']
theorem no_rational_place07 {t : ℚ} (ht : 1 < t) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpmod : ∀ i, p i % 8 = 1 ∨ p i % 8 = 7)
    (hDelta_gt : 1 < ∏ i, p i) (hDelta : (∏ i, p i) % 8 = 1) {qD : ℚ}
    (hdisc : t ^ 2 - 1 = ((∏ i, p i : ℕ) : ℚ) * qD ^ 2)
    (hrank : (primeLegendreMatrix p hp).rank = r - 1)
    (htint : ‖(t : ℚ_[37])‖ ≤ 1)
    (htres : padicResidue (t : ℚ_[37]) htint = 14 ∨
      padicResidue (t : ℚ_[37]) htint = -14 ∨
      padicResidue (t : ℚ_[37]) htint = 16 ∨
      padicResidue (t : ℚ_[37]) htint = -16) : ∀ w : Place ℚ (field ℚ t), ¬ w.IsRational := by
  intro w hw
  have empty := common_root_exclusion ht p hp hinj hpmod hDelta_gt hDelta
    hdisc hrank htint htres
  exact empty.false (rationalPlaceSource07 t ht w hw)

#print axioms no_rational_place07

#print axioms rationalPlaceSource07
end FourCorner.CommonLiteralField
