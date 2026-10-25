import FourCorner.RadiusModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace FourCorner

/-- The simultaneous-square coordinates, including all real signs and the exact metric. -/
structure PureCoordinates (p β U V W T : ℚ) : Prop where
  hp : 1 < p
  hβ : 1 < β
  hUpos : 0 < U
  hVpos : 0 < V
  hWpos : 0 < W
  hTpos : 0 < T
  hU2 : U ^ 2 = p * β
  hV2 : V ^ 2 = 2 * (p - 1) * (β - 1)
  hW2 : W ^ 2 = 2 * (p + 1) * (β + 1)
  hT2 : T ^ 2 = (p - 1) * β + p + 1
  hmetric : (4 * U + W * V) / T ^ 2 < 2

/-- A labelled rational point of the pure-coordinate model. -/
structure PurePoint where
  p : ℚ
  β : ℚ
  U : ℚ
  V : ℚ
  W : ℚ
  T : ℚ
  h : PureCoordinates p β U V W T

/-- A strict rational-distance point in the selected chamber, with all ordered radii. -/
structure ChamberPoint where
  x : ℚ
  y : ℚ
  r₀ : ℚ
  r₁ : ℚ
  r₂ : ℚ
  r₃ : ℚ
  h : StrictPoint x y r₀ r₁ r₂ r₃
  hsum : 1 < x + y
  hdiff : y < x

def pureX (U V W T : ℚ) : ℚ := 1 / 2 + (U + W * V / 4) / T ^ 2
def pureY (U V W T : ℚ) : ℚ := 1 / 2 + (U - W * V / 4) / T ^ 2
def pureR0 (U T : ℚ) : ℚ := (U + 1) / T
def pureR1 (V W T : ℚ) : ℚ := (W - V) / (2 * T)
def pureR2 (V W T : ℚ) : ℚ := (W + V) / (2 * T)
def pureR3 (U T : ℚ) : ℚ := (U - 1) / T

/-- Exact ordered four-square return; no positivity is needed for these identities. -/
theorem pure_fourSquares {p β U V W T : ℚ} (hT : T ≠ 0)
    (hU2 : U ^ 2 = p * β)
    (hV2 : V ^ 2 = 2 * (p - 1) * (β - 1))
    (hW2 : W ^ 2 = 2 * (p + 1) * (β + 1))
    (hT2 : T ^ 2 = (p - 1) * β + p + 1) :
    FourSquares (pureX U V W T) (pureY U V W T)
      (pureR0 U T) (pureR1 V W T) (pureR2 V W T) (pureR3 U T) := by
  have hmaster : 8 * (U ^ 2 + 1) * T ^ 2 =
      4 * (T ^ 2) ^ 2 + 16 * U ^ 2 + W ^ 2 * V ^ 2 := by
    rw [hU2, hV2, hW2, hT2]
    ring
  have hsum : W ^ 2 + V ^ 2 = 4 * U ^ 2 + 4 := by
    rw [hW2, hV2, hU2]
    ring
  unfold FourSquares pureX pureY pureR0 pureR1 pureR2 pureR3
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    field_simp
  · linear_combination 8 * hmaster
  · linear_combination 8 * hmaster + 16 * T ^ 2 * hsum
  · linear_combination 8 * hmaster + 16 * T ^ 2 * hsum
  · linear_combination 8 * hmaster

/-- The signs forced by positive simultaneous-square coordinates. -/
theorem PureCoordinates.root_bounds {p β U V W T : ℚ}
    (h : PureCoordinates p β U V W T) : 1 < U ∧ V < W := by
  have hp : 0 < p := lt_trans zero_lt_one h.hp
  have hb : 0 < β := lt_trans zero_lt_one h.hβ
  have hprod : 1 < p * β := by nlinarith [h.hp, h.hβ, mul_pos (sub_pos.mpr h.hp) (sub_pos.mpr h.hβ)]
  constructor
  · nlinarith [h.hU2, h.hUpos]
  · have hdelta : W ^ 2 - V ^ 2 = 4 * (p + β) := by
      rw [h.hW2, h.hV2]
      ring
    nlinarith [h.hWpos, h.hVpos]

/-- The literal metric inequality is equivalent to the denominator-cleared form. -/
theorem pure_metric_iff {U V W T : ℚ} (hT : 0 < T) :
    (4 * U + W * V) / T ^ 2 < 2 ↔ 2 * (U + W * V / 4) < T ^ 2 := by
  rw [div_lt_iff₀ (sq_pos_of_pos hT)]
  constructor <;> intro h <;> linarith

/-- The pure-coordinate model gives a strict point in the selected chamber. -/
theorem PureCoordinates.strictPoint {p β U V W T : ℚ}
    (h : PureCoordinates p β U V W T) :
    StrictPoint (pureX U V W T) (pureY U V W T)
      (pureR0 U T) (pureR1 V W T) (pureR2 V W T) (pureR3 U T) ∧
    1 < pureX U V W T + pureY U V W T ∧
    pureY U V W T < pureX U V W T := by
  obtain ⟨hU1, hVW⟩ := h.root_bounds
  have hu := h.hUpos
  have hv := h.hVpos
  have hw := h.hWpos
  have ht := h.hTpos
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos h.hTpos
  have hUV : 0 < (U + W * V / 4) / T ^ 2 := by
    apply div_pos _ hT2
    positivity
  have hx1 : pureX U V W T < 1 := by
    unfold pureX
    have hh := (pure_metric_iff h.hTpos).mp h.hmetric
    have hh' : (U + W * V / 4) / T ^ 2 < 1 / 2 := by
      apply (div_lt_iff₀ hT2).2
      linarith
    linarith
  have hsum : 1 < pureX U V W T + pureY U V W T := by
    have hu : 0 < U / T ^ 2 := div_pos h.hUpos hT2
    unfold pureX pureY
    rw [add_div, sub_div]
    linarith
  have hdiff : pureY U V W T < pureX U V W T := by
    have hv : 0 < (W * V / 4) / T ^ 2 := by positivity
    unfold pureX pureY
    rw [add_div, sub_div]
    linarith
  refine ⟨?_, hsum, hdiff⟩
  refine ⟨?_, hx1, ?_, lt_trans hdiff hx1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold pureX
    linarith
  · linarith
  · unfold pureR0
    exact div_pos (by linarith [h.hUpos]) h.hTpos
  · unfold pureR1
    exact div_pos (sub_pos.mpr hVW) (by positivity)
  · unfold pureR2
    exact div_pos (add_pos h.hWpos h.hVpos) (by positivity)
  · unfold pureR3
    exact div_pos (sub_pos.mpr hU1) h.hTpos
  · exact pure_fourSquares (ne_of_gt h.hTpos) h.hU2 h.hV2 h.hW2 h.hT2

/-- Diagonal inverse parameters with the original corner labels. -/
def radiusPureP (r₀ r₁ r₂ r₃ : ℚ) : ℚ :=
  (2 - (r₂ - r₁) ^ 2) / (r₀ - r₃) ^ 2
def radiusPureBeta (r₀ r₁ r₂ r₃ : ℚ) : ℚ :=
  (r₀ + r₃) ^ 2 / (2 - (r₂ - r₁) ^ 2)
def radiusPureU (r₀ r₃ : ℚ) : ℚ := (r₀ + r₃) / (r₀ - r₃)
def radiusPureV (r₀ r₁ r₂ r₃ : ℚ) : ℚ := 2 * (r₂ - r₁) / (r₀ - r₃)
def radiusPureW (r₀ r₁ r₂ r₃ : ℚ) : ℚ := 2 * (r₁ + r₂) / (r₀ - r₃)
def radiusPureT (r₀ r₃ : ℚ) : ℚ := 2 / (r₀ - r₃)

/-- Recovery from the ordered radii recovers every pure parameter, including root signs. -/
theorem PureCoordinates.recover_parameters {p β U V W T : ℚ}
    (h : PureCoordinates p β U V W T) :
    radiusPureP (pureR0 U T) (pureR1 V W T) (pureR2 V W T) (pureR3 U T) = p ∧
    radiusPureBeta (pureR0 U T) (pureR1 V W T) (pureR2 V W T) (pureR3 U T) = β ∧
    radiusPureU (pureR0 U T) (pureR3 U T) = U ∧
    radiusPureV (pureR0 U T) (pureR1 V W T) (pureR2 V W T) (pureR3 U T) = V ∧
    radiusPureW (pureR0 U T) (pureR1 V W T) (pureR2 V W T) (pureR3 U T) = W ∧
    radiusPureT (pureR0 U T) (pureR3 U T) = T := by
  have ht : T ≠ 0 := ne_of_gt h.hTpos
  have hp : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one h.hp)
  have hd : pureR0 U T - pureR3 U T = 2 / T := by
    unfold pureR0 pureR3
    ring
  have hs : pureR0 U T + pureR3 U T = 2 * U / T := by
    unfold pureR0 pureR3
    ring
  have he : pureR2 V W T - pureR1 V W T = V / T := by
    unfold pureR2 pureR1
    ring
  have hw : pureR1 V W T + pureR2 V W T = W / T := by
    unfold pureR2 pureR1
    ring
  have hden : 2 - (V / T) ^ 2 = 4 * p / T ^ 2 := by
    apply (eq_div_iff (pow_ne_zero _ ht)).2
    field_simp
    nlinarith [h.hT2, h.hV2]
  unfold radiusPureP radiusPureBeta radiusPureU radiusPureV radiusPureW radiusPureT
  rw [hd, hs, he, hw, hden]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    norm_num
  · field_simp
    nlinarith [h.hU2]
  all_goals field_simp

#print axioms PureCoordinates.recover_parameters
#print axioms pure_fourSquares
#print axioms PureCoordinates.strictPoint
end FourCorner
