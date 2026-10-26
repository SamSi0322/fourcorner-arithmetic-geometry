import OrderedEval
import SignedSquareClasses

open Polynomial WeierstrassCurve.Affine
namespace FourCorner.OrderedSplit
noncomputable section
variable {K : Type*} [Field K] {W : WeierstrassCurve.Affine K}

/-- A bijection of the actual etale algebra induces a bijection of square classes. -/
def squareEquiv (e : W.A ≃ₐ[K] (Fin 3 → K)) :
    W.M ≃* (Fin 3 → Units.modPow K 2) :=
  (Units.modPow.congr e.toMulEquiv 2).trans (Units.modPow.piEquiv (fun _ : Fin 3 => K) 2)

lemma squareEquiv_unit (e : W.A ≃ₐ[K] (Fin 3 → K)) {a : W.A}
    (ha : IsUnit a) (i : Fin 3) :
    squareEquiv e (ha.unit : W.M) i =
      (((ha.map e.toMonoidHom).map (Pi.evalMonoidHom (fun _ : Fin 3 => K) i)).unit :
        Units.modPow K 2) := by
  change Units.modPow.piEquiv (fun _ : Fin 3 => K) 2
    (QuotientGroup.mk (Units.map e.toMonoidHom ha.unit)) i = _
  rw [Units.modPow.piEquiv_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  rfl

/-- The signed square class of a nonzero scalar. -/
def scalarClass (a : K) (ha : a ≠ 0) : Units.modPow K 2 :=
  QuotientGroup.mk (Units.mk0 a ha)

lemma squareEquiv_unit_eq (e : W.A ≃ₐ[K] (Fin 3 → K)) {a : W.A}
    (ha : IsUnit a) (i : Fin 3) {b : K} (hb : b ≠ 0) (hab : e a i = b) :
    squareEquiv e (ha.unit : W.M) i = scalarClass b hb := by
  rw [squareEquiv_unit]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  exact hab

lemma scalarClass_mul (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    scalarClass a ha * scalarClass b hb = scalarClass (a * b) (mul_ne_zero ha hb) := by
  unfold scalarClass
  rw [← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Units.ext rfl)

lemma scalarClass_eq_one_iff (a : K) (ha : a ≠ 0) :
    scalarClass a ha = 1 ↔ IsSquare a :=
  Units.modPow.mk_eq_one_iff_isSquare

lemma scalarClass_eq_iff_exists (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    scalarClass a ha = scalarClass b hb ↔ ∃ q : K, a = b * q ^ 2 :=
  Units.modPow.signedUnits_mk0_eq_iff_exists a b ha hb

lemma scalarClass_eq_of_mul_square {a b q : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a = b * q ^ 2) : scalarClass a ha = scalarClass b hb :=
  (scalarClass_eq_iff_exists a b ha hb).mpr ⟨q, h⟩

lemma scalarClass_product_eq_one_iff (a : Fin 3 → K) (ha : ∀ i, a i ≠ 0) :
    (∏ i, scalarClass (a i) (ha i)) = 1 ↔ IsSquare (∏ i, a i) := by
  simp only [Fin.prod_univ_three]
  rw [scalarClass_mul, scalarClass_mul, scalarClass_eq_one_iff]

variable [DecidableEq K] [W.IsCharNeTwoNF] [W.IsElliptic]

/-- Ordered Kummer homomorphism, obtained from the actual elliptic group descent. -/
def delta (e : W.A ≃ₐ[K] (Fin 3 → K)) :
    Multiplicative W.Point →* (Fin 3 → Units.modPow K 2) :=
  (squareEquiv e).toMonoidHom.comp (μ (W := W))

lemma delta_apply (e : W.A ≃ₐ[K] (Fin 3 → K)) (P : W.Point) :
    delta e (Multiplicative.ofAdd P) = squareEquiv e (W.μ₀ P) := rfl

lemma delta_ker (e : W.A ≃ₐ[K] (Fin 3 → K)) :
    (delta e).ker = (nsmulAddMonoidHom (α := W.Point) 2).range.toSubgroup := by
  rw [← ker_μ_eq]
  ext P
  change squareEquiv e (μ P) = 1 ↔ μ P = 1
  exact (squareEquiv e).map_eq_one_iff

lemma delta_eq_one_iff_double (e : W.A ≃ₐ[K] (Fin 3 → K)) (P : W.Point) :
    delta e (Multiplicative.ofAdd P) = 1 ↔ ∃ Q : W.Point, 2 • Q = P := by
  change Multiplicative.ofAdd P ∈ (delta e).ker ↔ _
  rw [delta_ker]
  change P ∈ (nsmulAddMonoidHom (α := W.Point) 2).range ↔ _
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]

@[simp] lemma delta_zero (e : W.A ≃ₐ[K] (Fin 3 → K)) :
    delta e (Multiplicative.ofAdd (0 : W.Point)) = 1 := by
  rw [delta_apply, μ₀_zero, map_one]

variable (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i)))

/-- Actual ordered Kummer map at the supplied three distinct roots. -/
def orderedDelta : Multiplicative W.Point →* (Fin 3 → Units.modPow K 2) :=
  delta (orderedEval r hr hf)

lemma orderedDelta_ker :
    (orderedDelta r hr hf).ker =
      (nsmulAddMonoidHom (α := W.Point) 2).range.toSubgroup :=
  delta_ker _

lemma orderedDelta_eq_one_iff_double (P : W.Point) :
    orderedDelta r hr hf (Multiplicative.ofAdd P) = 1 ↔ ∃ Q : W.Point, 2 • Q = P :=
  delta_eq_one_iff_double _ P

include hr hf in
lemma coordinate_nonzero_of_nonroot {x : K} (hx : W.f.eval x ≠ 0) (i : Fin 3) :
    x - r i ≠ 0 := by
  intro he
  apply hx
  apply (eval_f_eq_zero_iff r hf x).mpr
  exact ⟨i, sub_eq_zero.mp he⟩

lemma orderedDelta_some_of_nonroot {x y : K} (hxy : W.Nonsingular x y)
    (hx : W.f.eval x ≠ 0) (i : Fin 3) :
    orderedDelta r hr hf (Multiplicative.ofAdd (Point.some x y hxy)) i =
      scalarClass (x - r i) (coordinate_nonzero_of_nonroot r hr hf hx i) := by
  change squareEquiv (orderedEval r hr hf) (W.μ₀ (Point.some x y hxy)) i = _
  rw [μ₀_some, μX_of_eval_f_ne_zero hx]
  apply squareEquiv_unit_eq (orderedEval r hr hf)
    (W.isUnit_mk_sub_X_of_eval_f_ne_zero hx) i
  change orderedEval r hr hf (AdjoinRoot.mk W.f (C x - X)) i = x - r i
  rw [orderedEval_mk]
  simp only [eval_sub, eval_C, eval_X]

/-- Torsion representative before simplifying its ordered coordinates. -/
lemma orderedDelta_some_of_root {x y : K} (hxy : W.Nonsingular x y)
    (hx : W.f.eval x = 0) (i : Fin 3) {b : K} (hb : b ≠ 0)
    (he : x - r i + (W.fCofactor x).eval (r i) = b) :
    orderedDelta r hr hf (Multiplicative.ofAdd (Point.some x y hxy)) i =
      scalarClass b hb := by
  change squareEquiv (orderedEval r hr hf) (W.μ₀ (Point.some x y hxy)) i = _
  rw [μ₀_some, μX_of_eval_f_eq_zero hx]
  apply squareEquiv_unit_eq (orderedEval r hr hf)
    (W.isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx) i
  rw [orderedEval_mk]
  simpa only [eval_add, eval_sub, eval_C, eval_X] using he

/-- The literal ordered rows at the three two-torsion abscissas. -/
def torsionRow (j : Fin 3) : Fin 3 → K :=
  (![![(r 0 - r 1) * (r 0 - r 2), r 0 - r 1, r 0 - r 2],
     ![r 1 - r 0, (r 1 - r 0) * (r 1 - r 2), r 1 - r 2],
     ![r 2 - r 0, r 2 - r 1, (r 2 - r 0) * (r 2 - r 1)]] : Fin 3 → Fin 3 → K) j

include hr in
lemma torsionRow_ne_zero (j i : Fin 3) : torsionRow r j i ≠ 0 := by
  have h01 : r 0 - r 1 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h02 : r 0 - r 2 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h10 : r 1 - r 0 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h12 : r 1 - r 2 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h20 : r 2 - r 0 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have h21 : r 2 - r 1 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  fin_cases j <;> fin_cases i <;> simp [torsionRow, *]

lemma orderedDelta_some_at_root (j : Fin 3) {y : K} (hxy : W.Nonsingular (r j) y)
    (i : Fin 3) :
    orderedDelta r hr hf (Multiplicative.ofAdd (Point.some (r j) y hxy)) i =
      scalarClass (torsionRow r j i) (torsionRow_ne_zero r hr j i) := by
  apply orderedDelta_some_of_root r hr hf hxy
    ((eval_f_eq_zero_iff r hf (r j)).mpr ⟨j, rfl⟩)
  obtain ⟨h0, h1, h2⟩ := W.fCofactor_eq_of_f_eq (rootFactorization r hf)
  fin_cases j <;> fin_cases i <;> simp [torsionRow, h0, h1, h2]

/-- The three ordered coordinates multiply to the trivial square class. -/
lemma orderedDelta_product (P : W.Point) :
    ∏ i, orderedDelta r hr hf (Multiplicative.ofAdd P) i = 1 := by
  cases P with
  | zero =>
      change ∏ i, delta (orderedEval r hr hf) (Multiplicative.ofAdd (0 : W.Point)) i = 1
      rw [delta_zero]
      simp
  | some x y hxy =>
      by_cases hx : W.f.eval x = 0
      · obtain ⟨j, rfl⟩ := (eval_f_eq_zero_iff r hf x).mp hx
        simp only [orderedDelta_some_at_root]
        apply (scalarClass_product_eq_one_iff (torsionRow r j) (torsionRow_ne_zero r hr j)).mpr
        fin_cases j <;> simp only [Fin.prod_univ_three, torsionRow, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val, Fin.reduceFinMk]
        · exact ⟨(r 0-r 1)*(r 0-r 2), by ring⟩
        · exact ⟨(r 1-r 0)*(r 1-r 2), by ring⟩
        · exact ⟨(r 2-r 0)*(r 2-r 1), by ring⟩
      · simp only [orderedDelta_some_of_nonroot r hr hf hxy hx]
        apply (scalarClass_product_eq_one_iff (fun i => x-r i)
          (coordinate_nonzero_of_nonroot r hr hf hx)).mpr
        have he := (W.equation_iff_eval_f_eq_sq x y).mp hxy.1
        rw [hf] at he
        simp only [eval_prod, eval_sub, eval_X, eval_C] at he
        exact ⟨y, by simpa only [sq] using he⟩

/-- The third coordinate can be discarded only on the proved product-one image. -/
lemma orderedDelta_eq_iff_first_two (P Q : W.Point) :
    orderedDelta r hr hf (Multiplicative.ofAdd P) =
      orderedDelta r hr hf (Multiplicative.ofAdd Q) ↔
    orderedDelta r hr hf (Multiplicative.ofAdd P) 0 =
      orderedDelta r hr hf (Multiplicative.ofAdd Q) 0 ∧
    orderedDelta r hr hf (Multiplicative.ofAdd P) 1 =
      orderedDelta r hr hf (Multiplicative.ofAdd Q) 1 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    have hP := orderedDelta_product r hr hf P
    have hQ := orderedDelta_product r hr hf Q
    rw [Fin.prod_univ_three, h0, h1] at hP
    rw [Fin.prod_univ_three] at hQ
    have h2 := mul_left_cancel (hP.trans hQ.symm)
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

#print axioms squareEquiv
#print axioms scalarClass_eq_iff_exists
#print axioms scalarClass_eq_of_mul_square
#print axioms orderedDelta_eq_iff_first_two
#print axioms orderedDelta_product
#print axioms orderedDelta_some_at_root
#print axioms orderedDelta_ker
#print axioms orderedDelta_some_of_nonroot
#print axioms orderedDelta_some_of_root
#print axioms delta_ker
#print axioms delta_eq_one_iff_double
end
end FourCorner.OrderedSplit
