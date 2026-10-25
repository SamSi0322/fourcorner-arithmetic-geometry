import FourCorner.RadiusModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

namespace FourCorner

/-- The literal congruent-number equation, with no abstract group hypotheses. -/
def CongruentEquation (n x y : ℚ) : Prop := y ^ 2 = x * (x - n) * (x + n)

def congruentCurve (n : ℚ) : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n ^ 2), 0⟩

theorem congruentEquation_iff_weierstrass (n x y : ℚ) :
    CongruentEquation n x y ↔ (congruentCurve n).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [congruentCurve, WeierstrassCurve.toAffine, CongruentEquation]
  constructor <;> intro h <;> nlinarith [h]

/-- Inverse map of the simultaneous-square model to the complete ordered source. -/
def sourceA (n p : ℚ) : ℚ := -n / p
def sourceB (n p k : ℚ) : ℚ := k * sourceA n p ^ 2
def sourceC (n β : ℚ) : ℚ := n * (β + 1) / (β - 1)
def sourceL (n β k U V W : ℚ) : ℚ := n / k * (U * V * W) / (β - 1) ^ 2
def sourceU (p k V W : ℚ) : ℚ := (p - 1) * W / (k * V)
def sourceV (p k V : ℚ) : ℚ := 2 * (p ^ 2 - 1) / (k * V)
def sourceH (U T : ℚ) : ℚ := T / (2 * U)

/-- The first elliptic point, retaining its ordinate. -/
theorem inverse_first_curve {n p k : ℚ} (hn : n ≠ 0) (hp : p ≠ 0)
    (hk : n * k ^ 2 = p * (p ^ 2 - 1)) :
    CongruentEquation n (sourceA n p) (sourceB n p k) := by
  have hk2 : k ^ 2 = p * (p ^ 2 - 1) / n := (eq_div_iff hn).2 (by nlinarith [hk])
  unfold CongruentEquation sourceA sourceB
  simp only [sourceA, mul_pow, div_pow, neg_sq, pow_mul]
  rw [hk2]
  field_simp
  <;> ring

/-- The second elliptic point, with the exact positive product ordinate. -/
theorem inverse_second_curve {n p β k U V W : ℚ}
    (hn : n ≠ 0) (hp : p ≠ 0) (hpm : p ^ 2 - 1 ≠ 0) (hβ : β - 1 ≠ 0)
    (hk : n * k ^ 2 = p * (p ^ 2 - 1))
    (hU : U ^ 2 = p * β) (hV : V ^ 2 = 2 * (p - 1) * (β - 1))
    (hW : W ^ 2 = 2 * (p + 1) * (β + 1)) :
    CongruentEquation n (sourceC n β) (sourceL n β k U V W) := by
  have hk2 : k ^ 2 = p * (p ^ 2 - 1) / n := (eq_div_iff hn).2 (by nlinarith [hk])
  unfold CongruentEquation sourceC sourceL
  simp only [div_pow, mul_pow]
  rw [hk2, hU, hV, hW]
  field_simp
  <;> ring

 theorem inverse_u_square {n p β k V W : ℚ}
    (hn : n ≠ 0) (hp : p ≠ 0) (hpm : p ^ 2 - 1 ≠ 0)
    (hpm1 : p - 1 ≠ 0) (hβ : β - 1 ≠ 0)
    (hk : n * k ^ 2 = p * (p ^ 2 - 1))
    (hV : V ^ 2 = 2 * (p - 1) * (β - 1))
    (hW : W ^ 2 = 2 * (p + 1) * (β + 1)) :
    sourceU p k V W ^ 2 = -(sourceA n p * sourceC n β) / n := by
  have hk2 : k ^ 2 = p * (p ^ 2 - 1) / n := (eq_div_iff hn).2 (by nlinarith [hk])
  unfold sourceU sourceA sourceC
  simp only [div_pow, mul_pow]
  rw [hk2, hV, hW]
  field_simp
  <;> ring

 theorem inverse_v_square {n p β k V : ℚ}
    (hn : n ≠ 0) (hp : p ≠ 0) (hpm : p ^ 2 - 1 ≠ 0)
    (hpm1 : p - 1 ≠ 0) (hβ : β - 1 ≠ 0)
    (hk : n * k ^ 2 = p * (p ^ 2 - 1))
    (hV : V ^ 2 = 2 * (p - 1) * (β - 1)) :
    sourceV p k V ^ 2 = -((sourceA n p - n) * (sourceC n β - n)) / n := by
  have hk2 : k ^ 2 = p * (p ^ 2 - 1) / n := (eq_div_iff hn).2 (by nlinarith [hk])
  unfold sourceV sourceA sourceC
  simp only [div_pow, mul_pow]
  rw [hk2, hV]
  field_simp
  <;> ring

 theorem inverse_h_square {n p β U T : ℚ}
    (hn : n ≠ 0) (hp : p ≠ 0) (hβ0 : β ≠ 0) (hβ : β - 1 ≠ 0)
    (hU : U ^ 2 = p * β) (hT : T ^ 2 = (p - 1) * β + p + 1) :
    sourceH U T ^ 2 = (sourceA n p + sourceC n β) / (2 * (sourceC n β + n)) := by
  unfold sourceH sourceA sourceC
  simp only [div_pow, mul_pow]
  rw [hU, hT]
  field_simp [hβ0]
  <;> ring

def ordinateW (n b ℓ u v : ℚ) : ℚ := b * ℓ / (n * u * v)
def pairP (n a : ℚ) : ℚ := -n / a
def pairK (a b : ℚ) : ℚ := b / a ^ 2
def pairBeta (n c : ℚ) : ℚ := (c + n) / (c - n)
def pairU (n a b ℓ u v : ℚ) : ℚ := (n - a) * ordinateW n b ℓ u v / (b * v)
def pairV (a b v : ℚ) : ℚ := -(2 * b) / (a * v)
def pairW (n a u v : ℚ) : ℚ := 2 * (a - n) * u / (a * v)
def pairT (n a b ℓ u v h : ℚ) : ℚ := 2 * pairU n a b ℓ u v * h

theorem ordinateW_square {n a b c ℓ u v : ℚ}
    (hn : n ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (ham : a - n ≠ 0) (hcm : c - n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c ℓ)
    (hu : u ^ 2 = -(a * c) / n) (hv : v ^ 2 = -((a - n) * (c - n)) / n) :
    ordinateW n b ℓ u v ^ 2 = (a + n) * (c + n) := by
  unfold ordinateW
  simp only [div_pow, mul_pow]
  rw [hQ, hR, hu, hv]
  field_simp
  <;> ring

theorem pairK_square {n a b : ℚ} (ha : a ≠ 0)
    (hQ : CongruentEquation n a b) :
    n * pairK a b ^ 2 = pairP n a * (pairP n a ^ 2 - 1) := by
  unfold pairK pairP
  simp only [div_pow]
  rw [hQ]
  field_simp
  <;> ring

theorem pairU_square {n a b c ℓ u v : ℚ}
    (ha : a ≠ 0) (ham : a - n ≠ 0) (hap : a + n ≠ 0) (hcm : c - n ≠ 0)
    (hn : n ≠ 0) (hQ : CongruentEquation n a b)
    (hv : v ^ 2 = -((a - n) * (c - n)) / n)
    (hw : ordinateW n b ℓ u v ^ 2 = (a + n) * (c + n)) :
    pairU n a b ℓ u v ^ 2 = pairP n a * pairBeta n c := by
  unfold pairU pairP pairBeta
  simp only [div_pow, mul_pow]
  rw [hw, hQ, hv]
  field_simp
  <;> ring

theorem pairV_square {n a b c v : ℚ}
    (ha : a ≠ 0) (ham : a - n ≠ 0) (hcm : c - n ≠ 0)
    (hn : n ≠ 0) (hQ : CongruentEquation n a b)
    (hv : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairV a b v ^ 2 = 2 * (pairP n a - 1) * (pairBeta n c - 1) := by
  unfold pairV pairP pairBeta
  simp only [div_pow, neg_sq, mul_pow]
  rw [hQ, hv]
  field_simp
  <;> ring

theorem pairW_square {n a c u v : ℚ}
    (ha : a ≠ 0) (ham : a - n ≠ 0) (hcm : c - n ≠ 0)
    (hn : n ≠ 0) (hu : u ^ 2 = -(a * c) / n)
    (hv : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairW n a u v ^ 2 = 2 * (pairP n a + 1) * (pairBeta n c + 1) := by
  unfold pairW pairP pairBeta
  simp only [div_pow, mul_pow]
  rw [hu, hv]
  field_simp
  <;> ring

theorem pairT_square {n a b c ℓ u v h : ℚ}
    (ha : a ≠ 0) (hcm : c - n ≠ 0) (hcp : c + n ≠ 0)
    (hU : pairU n a b ℓ u v ^ 2 = pairP n a * pairBeta n c)
    (hh : h ^ 2 = (a + c) / (2 * (c + n))) :
    pairT n a b ℓ u v h ^ 2 =
      (pairP n a - 1) * pairBeta n c + pairP n a + 1 := by
  unfold pairT
  simp only [mul_pow]
  rw [hU, hh]
  unfold pairP pairBeta
  field_simp
  <;> ring

/-- Cancellation of the first product root uses the ordered second slot. -/
theorem pairU_simplified {n a b c ℓ u v : ℚ}
    (hn : n ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcm : c - n ≠ 0)
    (hv2 : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairU n a b ℓ u v = ℓ / (u * (c - n)) := by
  have hvn : n * v ^ 2 = -((a - n) * (c - n)) := by
    have hh := (eq_div_iff hn).mp hv2
    nlinarith [hh]
  unfold pairU ordinateW
  field_simp
  linear_combination -ℓ * hvn

theorem pairT_square_simplified {n a b c ℓ u v h : ℚ}
    (ha : a ≠ 0) (hcm : c - n ≠ 0)
    (hT : pairT n a b ℓ u v h ^ 2 =
      (pairP n a - 1) * pairBeta n c + pairP n a + 1) :
    pairT n a b ℓ u v h ^ 2 = -2 * n * (a + c) / (a * (c - n)) := by
  rw [hT]
  unfold pairP pairBeta
  field_simp
  <;> ring

theorem pairWV_simplified {n a b c u v : ℚ}
    (hn : n ≠ 0) (ha : a ≠ 0) (hv : v ≠ 0) (hcm : c - n ≠ 0)
    (hv2 : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairW n a u v * pairV a b v = 4 * b * n * u / (a ^ 2 * (c - n)) := by
  have hvn : n * v ^ 2 = -((a - n) * (c - n)) := by
    have hh := (eq_div_iff hn).mp hv2
    nlinarith [hh]
  unfold pairW pairV
  field_simp
  linear_combination -4 * b * u * hvn

/-- Both real-metric contributions use the same original pair and the same u. -/
theorem pair_metric_identity {n a b c ℓ u v h : ℚ}
    (hn : n ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hu : u ≠ 0) (hac : a + c ≠ 0) (hcm : c - n ≠ 0)
    (hU : pairU n a b ℓ u v = ℓ / (u * (c - n)))
    (hWV : pairW n a u v * pairV a b v = 4 * b * n * u / (a ^ 2 * (c - n)))
    (hT : pairT n a b ℓ u v h ^ 2 = -2 * n * (a + c) / (a * (c - n)))
    (hu2 : u ^ 2 = -(a * c) / n) :
    (4 * pairU n a b ℓ u v + pairW n a u v * pairV a b v) /
        pairT n a b ℓ u v h ^ 2 =
      (2 * u / (a + c)) * (-b / a + ℓ / c) := by
  rw [hU, hWV, hT]
  have hun : n * u ^ 2 = -(a * c) := by
    have hh := (eq_div_iff hn).mp hu2
    nlinarith [hh]
  field_simp
  linear_combination -4 * a * ℓ * hun

theorem inverse_source_signs {n p β k U V W T : ℚ}
    (hn : 0 < n) (hp : 1 < p) (hβ : 1 < β) (hk : 0 < k)
    (hU : 0 < U) (hV : 0 < V) (hW : 0 < W) (hT : 0 < T) :
    -n < sourceA n p ∧ sourceA n p < 0 ∧ n < sourceC n β ∧
    0 < sourceB n p k ∧ 0 < sourceL n β k U V W ∧
    0 < sourceU p k V W ∧ 0 < sourceV p k V ∧ 0 < sourceH U T := by
  have hp0 : 0 < p := by linarith
  have hβm : 0 < β - 1 := by linarith
  have ha : sourceA n p < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hn) hp0
  refine ⟨?_, ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sourceA
    apply (lt_div_iff₀ hp0).2
    nlinarith
  · unfold sourceC
    apply (lt_div_iff₀ hβm).2
    nlinarith
  · exact mul_pos hk (sq_pos_of_ne_zero (ne_of_lt ha))
  · unfold sourceL
    positivity
  · unfold sourceU
    exact div_pos (mul_pos (by linarith) hW) (mul_pos hk hV)
  · unfold sourceV
    apply div_pos _ (mul_pos hk hV)
    have : 0 < p ^ 2 - 1 := by nlinarith
    positivity
  · exact div_pos hT (mul_pos (by norm_num) hU)

theorem forward_source_signs {n a b c ℓ u v h : ℚ}
    (hn : 0 < n) (han : -n < a) (ha : a < 0) (hc : n < c)
    (hb : 0 < b) (hℓ : 0 < ℓ) (hu : 0 < u) (hv : 0 < v) (hh : 0 < h) :
    1 < pairP n a ∧ 1 < pairBeta n c ∧ 0 < pairK a b ∧
    0 < pairU n a b ℓ u v ∧ 0 < pairV a b v ∧
    0 < pairW n a u v ∧ 0 < pairT n a b ℓ u v h := by
  have hcm : 0 < c - n := by linarith
  have hw : 0 < ordinateW n b ℓ u v := div_pos (mul_pos hb hℓ) (mul_pos (mul_pos hn hu) hv)
  have hU : 0 < pairU n a b ℓ u v := by
    exact div_pos (mul_pos (by linarith) hw) (mul_pos hb hv)
  refine ⟨?_, ?_, ?_, hU, ?_, ?_, ?_⟩
  · unfold pairP
    apply (lt_div_iff_of_neg ha).2
    linarith
  · unfold pairBeta
    apply (lt_div_iff₀ hcm).2
    linarith
  · exact div_pos hb (sq_pos_of_ne_zero (ne_of_lt ha))
  · exact div_pos_of_neg_of_neg (by nlinarith) (mul_neg_of_neg_of_pos ha hv)
  · apply div_pos_of_neg_of_neg _ (mul_neg_of_neg_of_pos ha hv)
    have : a - n < 0 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) this) hu
  · exact mul_pos (mul_pos (by norm_num) hU) hh

theorem positive_eq_of_sq_eq {a b : ℚ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 = b ^ 2) : a = b := by nlinarith

theorem recover_sourceA {n a : ℚ} (hn : n ≠ 0) (ha : a ≠ 0) :
    sourceA n (pairP n a) = a := by unfold sourceA pairP; field_simp

theorem recover_sourceB {n a b : ℚ} (hn : n ≠ 0) (ha : a ≠ 0) :
    sourceB n (pairP n a) (pairK a b) = b := by
  unfold sourceB
  rw [recover_sourceA hn ha]
  unfold pairK
  field_simp

theorem recover_sourceC {n c : ℚ} (hn : n ≠ 0) (hc : c - n ≠ 0) :
    sourceC n (pairBeta n c) = c := by
  unfold sourceC pairBeta
  field_simp [hn]
  <;> ring

theorem recover_pairP {n p : ℚ} (hn : n ≠ 0) (hp : p ≠ 0) :
    pairP n (sourceA n p) = p := by unfold sourceA pairP; field_simp

theorem recover_pairK {n p k : ℚ} (hn : n ≠ 0) (hp : p ≠ 0) :
    pairK (sourceA n p) (sourceB n p k) = k := by
  simp only [sourceB, sourceA, pairK]
  field_simp

theorem recover_pairBeta {n β : ℚ} (hn : n ≠ 0) (hβ : β - 1 ≠ 0) :
    pairBeta n (sourceC n β) = β := by
  unfold sourceC pairBeta
  field_simp [hn]
  <;> ring

#print axioms pair_metric_identity
#print axioms inverse_source_signs
#print axioms forward_source_signs
#print axioms ordinateW_square
#print axioms pairK_square
#print axioms pairU_square
#print axioms pairV_square
#print axioms pairW_square
#print axioms pairT_square
#print axioms inverse_first_curve
#print axioms inverse_second_curve
#print axioms inverse_u_square
#print axioms inverse_v_square
#print axioms inverse_h_square
end FourCorner
