import FourCorner.OrderedSourceAlgebra
import FourCorner.RationalSquarefree
import FourCorner.PureSource

namespace FourCorner

/-- Actual ordered affine rational points, with positive roots in the stated chamber. -/
@[ext] structure OrderedCore (n : ℚ) where
  a : ℚ
  b : ℚ
  c : ℚ
  ℓ : ℚ
  u : ℚ
  v : ℚ
  h : ℚ
  hn : 0 < n
  han : -n < a
  ha : a < 0
  hc : n < c
  hb : 0 < b
  hℓ : 0 < ℓ
  hu : 0 < u
  hv : 0 < v
  hh : 0 < h
  hQ : CongruentEquation n a b
  hR : CongruentEquation n c ℓ
  hu2 : u ^ 2 = -(a * c) / n
  hv2 : v ^ 2 = -((a - n) * (c - n)) / n
  hh2 : h ^ 2 = (a + c) / (2 * (c + n))

/-- The positive simultaneous-square coordinates, retaining their normalization. -/
@[ext] structure PureCore (n : ℚ) where
  p : ℚ
  β : ℚ
  k : ℚ
  U : ℚ
  V : ℚ
  W : ℚ
  T : ℚ
  hn : 0 < n
  hp : 1 < p
  hβ : 1 < β
  hk : 0 < k
  hU : 0 < U
  hV : 0 < V
  hW : 0 < W
  hT : 0 < T
  hk2 : n * k ^ 2 = p * (p ^ 2 - 1)
  hU2 : U ^ 2 = p * β
  hV2 : V ^ 2 = 2 * (p - 1) * (β - 1)
  hW2 : W ^ 2 = 2 * (p + 1) * (β + 1)
  hT2 : T ^ 2 = (p - 1) * β + p + 1

namespace OrderedCore
variable {n : ℚ} (s : OrderedCore n)
theorem n_ne (s : OrderedCore n) : n ≠ 0 := ne_of_gt s.hn
theorem a_ne : s.a ≠ 0 := ne_of_lt s.ha
theorem c_ne : s.c ≠ 0 := ne_of_gt (lt_trans s.hn s.hc)
theorem am_ne : s.a - n ≠ 0 := ne_of_lt (by linarith [s.ha, s.hn])
theorem ap_ne : s.a + n ≠ 0 := ne_of_gt (by linarith [s.han])
theorem cm_ne : s.c - n ≠ 0 := ne_of_gt (by linarith [s.hc])
theorem cp_ne : s.c + n ≠ 0 := ne_of_gt (by linarith [s.hc, s.hn])
theorem ac_ne : s.a + s.c ≠ 0 := ne_of_gt (by linarith [s.hc, s.han])

def toPure : PureCore n := by
  have H := forward_source_signs s.hn s.han s.ha s.hc s.hb s.hℓ s.hu s.hv s.hh
  have hw := ordinateW_square s.n_ne s.a_ne s.c_ne s.am_ne s.cm_ne s.hQ s.hR s.hu2 s.hv2
  have hU := pairU_square s.a_ne s.am_ne s.ap_ne s.cm_ne s.n_ne s.hQ s.hv2 hw
  exact {
    p := pairP n s.a, β := pairBeta n s.c, k := pairK s.a s.b
    U := pairU n s.a s.b s.ℓ s.u s.v, V := pairV s.a s.b s.v
    W := pairW n s.a s.u s.v, T := pairT n s.a s.b s.ℓ s.u s.v s.h
    hn := s.hn, hp := H.1, hβ := H.2.1, hk := H.2.2.1, hU := H.2.2.2.1
    hV := H.2.2.2.2.1, hW := H.2.2.2.2.2.1, hT := H.2.2.2.2.2.2
    hk2 := pairK_square s.a_ne s.hQ, hU2 := hU
    hV2 := pairV_square s.a_ne s.am_ne s.cm_ne s.n_ne s.hQ s.hv2
    hW2 := pairW_square s.a_ne s.am_ne s.cm_ne s.n_ne s.hu2 s.hv2
    hT2 := pairT_square s.a_ne s.cm_ne s.cp_ne hU s.hh2 }

/-- The original metric is exactly the simultaneous-square strict metric. -/
theorem metric_identity : (4 * s.toPure.U + s.toPure.W * s.toPure.V) / s.toPure.T ^ 2 =
    (2 * s.u / (s.a + s.c)) * (-s.b / s.a + s.ℓ / s.c) := by
  apply pair_metric_identity s.n_ne s.a_ne s.c_ne (ne_of_gt s.hu) s.ac_ne s.cm_ne
  · exact pairU_simplified s.n_ne (ne_of_gt s.hb) (ne_of_gt s.hu) (ne_of_gt s.hv) s.cm_ne s.hv2
  · exact pairWV_simplified s.n_ne s.a_ne (ne_of_gt s.hv) s.cm_ne s.hv2
  · exact pairT_square_simplified s.a_ne s.cm_ne s.toPure.hT2
  · exact s.hu2
end OrderedCore

namespace PureCore
variable {n : ℚ} (s : PureCore n)
theorem n_ne (s : PureCore n) : n ≠ 0 := ne_of_gt s.hn
theorem p_ne : s.p ≠ 0 := ne_of_gt (by linarith [s.hp])
theorem β_ne : s.β ≠ 0 := ne_of_gt (by linarith [s.hβ])
theorem pm_ne : s.p - 1 ≠ 0 := ne_of_gt (by linarith [s.hp])
theorem pm2_ne : s.p ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith [s.hp])
theorem βm_ne : s.β - 1 ≠ 0 := ne_of_gt (by linarith [s.hβ])

def toOrdered : OrderedCore n := by
  have H := inverse_source_signs s.hn s.hp s.hβ s.hk s.hU s.hV s.hW s.hT
  exact {
    a := sourceA n s.p, b := sourceB n s.p s.k, c := sourceC n s.β
    ℓ := sourceL n s.β s.k s.U s.V s.W, u := sourceU s.p s.k s.V s.W
    v := sourceV s.p s.k s.V, h := sourceH s.U s.T
    hn := s.hn, han := H.1, ha := H.2.1, hc := H.2.2.1, hb := H.2.2.2.1
    hℓ := H.2.2.2.2.1, hu := H.2.2.2.2.2.1, hv := H.2.2.2.2.2.2.1
    hh := H.2.2.2.2.2.2.2
    hQ := inverse_first_curve s.n_ne s.p_ne s.hk2
    hR := inverse_second_curve s.n_ne s.p_ne s.pm2_ne s.βm_ne s.hk2 s.hU2 s.hV2 s.hW2
    hu2 := inverse_u_square s.n_ne s.p_ne s.pm2_ne s.pm_ne s.βm_ne s.hk2 s.hV2 s.hW2
    hv2 := inverse_v_square s.n_ne s.p_ne s.pm2_ne s.pm_ne s.βm_ne s.hk2 s.hV2
    hh2 := inverse_h_square s.n_ne s.p_ne s.β_ne s.βm_ne s.hU2 s.hT2 }

@[simp] theorem roundtrip_p : s.toOrdered.toPure.p = s.p := recover_pairP s.n_ne s.p_ne
@[simp] theorem roundtrip_β : s.toOrdered.toPure.β = s.β := recover_pairBeta s.n_ne s.βm_ne
@[simp] theorem roundtrip_k : s.toOrdered.toPure.k = s.k := recover_pairK s.n_ne s.p_ne
@[simp] theorem roundtrip_U : s.toOrdered.toPure.U = s.U := by
  apply positive_eq_of_sq_eq s.toOrdered.toPure.hU s.hU
  rw [s.toOrdered.toPure.hU2, s.hU2, s.roundtrip_p, s.roundtrip_β]
@[simp] theorem roundtrip_V : s.toOrdered.toPure.V = s.V := by
  apply positive_eq_of_sq_eq s.toOrdered.toPure.hV s.hV
  rw [s.toOrdered.toPure.hV2, s.hV2, s.roundtrip_p, s.roundtrip_β]
@[simp] theorem roundtrip_W : s.toOrdered.toPure.W = s.W := by
  apply positive_eq_of_sq_eq s.toOrdered.toPure.hW s.hW
  rw [s.toOrdered.toPure.hW2, s.hW2, s.roundtrip_p, s.roundtrip_β]
@[simp] theorem roundtrip_T : s.toOrdered.toPure.T = s.T := by
  apply positive_eq_of_sq_eq s.toOrdered.toPure.hT s.hT
  rw [s.toOrdered.toPure.hT2, s.hT2, s.roundtrip_p, s.roundtrip_β]
@[simp] theorem roundtrip : s.toOrdered.toPure = s := by
  ext <;> simp only [roundtrip_p, roundtrip_β, roundtrip_k, roundtrip_U,
    roundtrip_V, roundtrip_W, roundtrip_T]
end PureCore

namespace OrderedCore
variable {n : ℚ} (s : OrderedCore n)
@[simp] theorem roundtrip_a : s.toPure.toOrdered.a = s.a := recover_sourceA s.n_ne s.a_ne
@[simp] theorem roundtrip_b : s.toPure.toOrdered.b = s.b := recover_sourceB s.n_ne s.a_ne
@[simp] theorem roundtrip_c : s.toPure.toOrdered.c = s.c := recover_sourceC s.n_ne s.cm_ne
@[simp] theorem roundtrip_ℓ : s.toPure.toOrdered.ℓ = s.ℓ := by
  apply positive_eq_of_sq_eq s.toPure.toOrdered.hℓ s.hℓ
  rw [s.toPure.toOrdered.hR, s.hR, s.roundtrip_c]
@[simp] theorem roundtrip_u : s.toPure.toOrdered.u = s.u := by
  apply positive_eq_of_sq_eq s.toPure.toOrdered.hu s.hu
  rw [s.toPure.toOrdered.hu2, s.hu2, s.roundtrip_a, s.roundtrip_c]
@[simp] theorem roundtrip_v : s.toPure.toOrdered.v = s.v := by
  apply positive_eq_of_sq_eq s.toPure.toOrdered.hv s.hv
  rw [s.toPure.toOrdered.hv2, s.hv2, s.roundtrip_a, s.roundtrip_c]
@[simp] theorem roundtrip_h : s.toPure.toOrdered.h = s.h := by
  apply positive_eq_of_sq_eq s.toPure.toOrdered.hh s.hh
  rw [s.toPure.toOrdered.hh2, s.hh2, s.roundtrip_a, s.roundtrip_c]
@[simp] theorem roundtrip : s.toPure.toOrdered = s := by
  ext <;> simp only [roundtrip_a, roundtrip_b, roundtrip_c, roundtrip_ℓ,
    roundtrip_u, roundtrip_v, roundtrip_h]
end OrderedCore

/-- The actual sign-sensitive bijection; ordinates and all three roots are retained. -/
def orderedPureEquiv (n : ℚ) : OrderedCore n ≃ PureCore n where
  toFun := OrderedCore.toPure
  invFun := PureCore.toOrdered
  left_inv := OrderedCore.roundtrip
  right_inv := PureCore.roundtrip

/-- The exact real metric on the original ordered pair. -/
def OrderedMetric {n : ℚ} (s : OrderedCore n) : Prop :=
    (2 * s.u / (s.a + s.c)) * (-s.b / s.a + s.ℓ / s.c) < 2

def PureMetric {n : ℚ} (s : PureCore n) : Prop :=
    (4 * s.U + s.W * s.V) / s.T ^ 2 < 2

/-- The bijection restricted by the original strict metric, not a weaker local condition. -/
def orderedPureStrictEquiv (n : ℚ) : {s : OrderedCore n // OrderedMetric s} ≃
    {s : PureCore n // PureMetric s} where
  toFun s := ⟨s.1.toPure, by simpa only [PureMetric, OrderedMetric, s.1.metric_identity] using s.2⟩
  invFun s := ⟨s.1.toOrdered, by
    change (2 * s.1.toOrdered.u / (s.1.toOrdered.a + s.1.toOrdered.c)) *
      (-s.1.toOrdered.b / s.1.toOrdered.a + s.1.toOrdered.ℓ / s.1.toOrdered.c) < 2
    rw [← s.1.toOrdered.metric_identity, PureCore.roundtrip]
    exact s.2⟩
  left_inv s := by apply Subtype.ext; exact s.1.roundtrip
  right_inv s := by apply Subtype.ext; exact s.1.roundtrip

/-- The first coordinate point is a nonsingular point in mathlib's affine model. -/
theorem OrderedCore.first_nonsingular {n : ℚ} (s : OrderedCore n) :
    (congruentCurve n).toAffine.Nonsingular s.a s.b := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨(congruentEquation_iff_weierstrass n s.a s.b).mp s.hQ, Or.inr ?_⟩
  simp only [congruentCurve, WeierstrassCurve.toAffine, zero_mul, sub_zero]
  linarith [s.hb]

/-- The second coordinate point is nonsingular as well, with its own actual ordinate. -/
theorem OrderedCore.second_nonsingular {n : ℚ} (s : OrderedCore n) :
    (congruentCurve n).toAffine.Nonsingular s.c s.ℓ := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨(congruentEquation_iff_weierstrass n s.c s.ℓ).mp s.hR, Or.inr ?_⟩
  simp only [congruentCurve, WeierstrassCurve.toAffine, zero_mul, sub_zero]
  linarith [s.hℓ]

/-- A normalized pure source with metric is exactly an instance of the pure model. -/
theorem PureCore.pureCoordinates {n : ℚ} (s : PureCore n) (hm : PureMetric s) :
    PureCoordinates s.p s.β s.U s.V s.W s.T :=
  ⟨s.hp, s.hβ, s.hU, s.hV, s.hW, s.hT, s.hU2, s.hV2, s.hW2, s.hT2, hm⟩

/-- The original strict four-radius point, produced from the actual ordered pair. -/
theorem OrderedCore.strictPoint {n : ℚ} (s : OrderedCore n) (hm : OrderedMetric s) :
    StrictPoint (pureX s.toPure.U s.toPure.V s.toPure.W s.toPure.T)
      (pureY s.toPure.U s.toPure.V s.toPure.W s.toPure.T)
      (pureR0 s.toPure.U s.toPure.T) (pureR1 s.toPure.V s.toPure.W s.toPure.T)
      (pureR2 s.toPure.V s.toPure.W s.toPure.T) (pureR3 s.toPure.U s.toPure.T) ∧
    1 < pureX s.toPure.U s.toPure.V s.toPure.W s.toPure.T +
      pureY s.toPure.U s.toPure.V s.toPure.W s.toPure.T ∧
    pureY s.toPure.U s.toPure.V s.toPure.W s.toPure.T <
      pureX s.toPure.U s.toPure.V s.toPure.W s.toPure.T := by
  apply PureCoordinates.strictPoint
  apply s.toPure.pureCoordinates
  unfold PureMetric
  rw [s.metric_identity]
  exact hm

/-- The positive diagonal sum is the reciprocal of the actual final-square root. -/
theorem OrderedCore.diagonal_sum {n : ℚ} (s : OrderedCore n) :
    pureR0 s.toPure.U s.toPure.T + pureR3 s.toPure.U s.toPure.T = 1 / s.h := by
  have hU : pairU n s.a s.b s.ℓ s.u s.v ≠ 0 := ne_of_gt s.toPure.hU
  have hh := ne_of_gt s.hh
  change (pairU n s.a s.b s.ℓ s.u s.v + 1) / (2 * pairU n s.a s.b s.ℓ s.u s.v * s.h) +
      (pairU n s.a s.b s.ℓ s.u s.v - 1) / (2 * pairU n s.a s.b s.ℓ s.u s.v * s.h) = 1 / s.h
  field_simp
  <;> ring

/-- Exact final square, with the positive radii attached to the same pair. -/
theorem OrderedCore.final_square {n : ℚ} (s : OrderedCore n) :
    (s.a + s.c) / (2 * (s.c + n)) =
      1 / (pureR0 s.toPure.U s.toPure.T + pureR3 s.toPure.U s.toPure.T) ^ 2 := by
  rw [s.diagonal_sum, ← s.hh2]
  simp

/-- Canonical positive squarefree normalization of every pure coordinate point. -/
theorem pureCoordinates_normalization {p β U V W T : ℚ}
    (h : PureCoordinates p β U V W T) :
    ∃! nk : ℕ × ℚ, 0 < nk.1 ∧ Squarefree nk.1 ∧ 0 < nk.2 ∧
      (nk.1 : ℚ) * nk.2 ^ 2 = p * (p ^ 2 - 1) := by
  have ht : 0 < p * (p ^ 2 - 1) := by
    apply mul_pos (by linarith [h.hp])
    nlinarith [h.hp]
  simpa only [eq_comm] using positive_rat_exists_unique_squarefree_pair ht

#print axioms OrderedCore.first_nonsingular
#print axioms OrderedCore.second_nonsingular
#print axioms OrderedCore.strictPoint
#print axioms OrderedCore.final_square
#print axioms pureCoordinates_normalization
#print axioms orderedPureEquiv
#print axioms orderedPureStrictEquiv
#print axioms OrderedCore.metric_identity
end FourCorner
