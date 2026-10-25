import FourCorner.IntegralModel
import FourCorner.CornerContent
import FourCorner.PrimitiveCongruences
import FourCorner.GaussianConverse
import FourCorner.SquarefreePart
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FourCorner

/-- A primitive integral right triangle with odd first leg has an integral
Gaussian square root, with norm exactly the positive hypotenuse. -/
theorem primitive_gaussian_square {a b r : ℤ}
    (h : PythagoreanTriple a b r) (hcop : Int.gcd a b = 1)
    (ha : a % 2 = 1) (hr : 0 < r) :
    ∃ q : GaussianInt, q ≠ 0 ∧ (⟨a, b⟩ : GaussianInt) = q ^ 2 ∧
      Zsqrtd.norm q = r := by
  obtain ⟨u, v, hu, hv, hr', _⟩ := h.coprime_classification' hcop ha hr
  refine ⟨⟨u, v⟩, ?_, ?_, ?_⟩
  · intro hz
    have hu0 : u = 0 := congrArg Zsqrtd.re hz
    have hv0 : v = 0 := congrArg Zsqrtd.im hz
    simp [hu0, hv0] at hr'
    omega
  · apply Zsqrtd.ext <;> simp [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul] <;>
      nlinarith
  · simp [Zsqrtd.norm]
    nlinarith

/-- The common gcd can be divided out before extracting the Gaussian root.
This theorem starts with the actual integer Pythagorean equation. -/
theorem gaussian_square_after_content {a b r : ℤ}
    (h : PythagoreanTriple a b r) (ha : a % 2 = 1) (hr : 0 < r) :
    ∃ q : GaussianInt, q ≠ 0 ∧
      (⟨a, b⟩ : GaussianInt) = (Int.gcd a b : GaussianInt) * q ^ 2 ∧
      r = (Int.gcd a b : ℤ) * Zsqrtd.norm q := by
  let d := Int.gcd a b
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hz : a = 0 := (Int.gcd_eq_zero_iff.mp hd0).1
    simp [hz] at ha
  have ha_eq : a / (d : ℤ) * d = a := Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hb_eq : b / (d : ℤ) * d = b := Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hr_eq : r / (d : ℤ) * d = r := Int.ediv_mul_cancel h.gcd_dvd
  have hna : a / (d : ℤ) % 2 = 1 := by
    have he := congrArg (fun z : ℤ => z % 2) ha_eq
    rw [Int.mul_emod, ha] at he
    have h1 := Int.emod_nonneg (a / (d : ℤ)) (by norm_num : (2 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos (a / (d : ℤ)) (by norm_num : (0 : ℤ) < 2)
    have h3 := Int.emod_nonneg (d : ℤ) (by norm_num : (2 : ℤ) ≠ 0)
    have h4 := Int.emod_lt_of_pos (d : ℤ) (by norm_num : (0 : ℤ) < 2)
    by_contra hn
    have hz : a / (d : ℤ) % 2 = 0 := by omega
    simp [hz] at he
  have hnr : 0 < r / (d : ℤ) := Int.ediv_pos_of_pos_of_dvd hr (Int.natCast_nonneg d) h.gcd_dvd
  obtain ⟨q, hq, hsq, hn⟩ := primitive_gaussian_square h.normalize
    (Int.gcd_div_gcd_div_gcd hd) hna hnr
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← hsq]
    apply Zsqrtd.ext <;> simp
    · exact ((mul_comm _ _).trans ha_eq).symm
    · exact ((mul_comm _ _).trans hb_eq).symm
  · rw [hn, mul_comm]
    exact hr_eq.symm

/-- Removing the square factor of the actual gcd gives the canonical positive
squarefree multiplier, not a freely chosen Gaussian square class. -/
theorem canonical_gaussian_square {a b r : ℤ}
    (h : PythagoreanTriple a b r) (ha : a % 2 = 1) (hr : 0 < r) :
    ∃ q : GaussianInt, q ≠ 0 ∧
      (⟨a, b⟩ : GaussianInt) = (squarefreePart (Int.gcd a b) : GaussianInt) * q ^ 2 ∧
      r = (squarefreePart (Int.gcd a b) : ℤ) * Zsqrtd.norm q ∧
      0 < Zsqrtd.norm q := by
  obtain ⟨q, hq, hroot, hrnorm⟩ := gaussian_square_after_content h ha hr
  have hd : 0 < Int.gcd a b := by
    apply Nat.pos_of_ne_zero
    intro hd0
    have hz : a = 0 := (Int.gcd_eq_zero_iff.mp hd0).1
    simp [hz] at ha
  obtain ⟨t, ht, hd⟩ := squarefreePart_decomposition_pos hd
  have htG : (t : GaussianInt) ≠ 0 := by
    intro hz
    have htz : (t : ℤ) = 0 := congrArg Zsqrtd.re hz
    have : t = 0 := by exact_mod_cast htz
    omega
  refine ⟨(t : GaussianInt) * q, mul_ne_zero htG hq, ?_, ?_,
    GaussianInt.norm_pos.mpr (mul_ne_zero htG hq)⟩
  · rw [hroot]
    conv_lhs => rw [hd]
    push_cast
    ring
  · rw [hrnorm, Zsqrtd.norm_mul]
    conv_lhs => rw [hd]
    simp only [Nat.cast_mul, Nat.cast_pow]
    change _ = _ * (((t : ℤ) * t) * Zsqrtd.norm q)
    ring

/-- Equality of the nonzero Gaussian rational `a + i b` with the rational
representative `s`, modulo a nonzero square in Q(i).  The two rational
coordinates are written explicitly, avoiding an opaque quotient type. -/
def GaussianRationalSquareClass (a b s : ℚ) : Prop :=
  s ≠ 0 ∧ ∃ u v : ℚ, (u ≠ 0 ∨ v ≠ 0) ∧
    a = s * (u ^ 2 - v ^ 2) ∧ b = s * (2 * u * v)

/-- The root `q/L` witnesses the representative `L*m`, including the common
coordinate denominator, in Q(i) modulo squares. -/
theorem gaussian_squareclass_denominator {a b L : ℤ} {m : ℕ} {q : GaussianInt}
    (hL : L ≠ 0) (hm : 0 < m) (hq : q ≠ 0)
    (hroot : (⟨a, b⟩ : GaussianInt) = (m : GaussianInt) * q ^ 2) :
    GaussianRationalSquareClass ((a : ℚ) / L) ((b : ℚ) / L) ((L : ℚ) * m) := by
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast hL
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hre : a = (m : ℤ) * (q.re ^ 2 - q.im ^ 2) := by
    have h := congrArg Zsqrtd.re hroot
    simpa [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul, sub_eq_add_neg, mul_assoc] using h
  have him : b = (m : ℤ) * (2 * q.re * q.im) := by
    have h := congrArg Zsqrtd.im hroot
    simp [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul] at h
    nlinarith
  refine ⟨mul_ne_zero hLQ hmQ, (q.re : ℚ) / L, (q.im : ℚ) / L, ?_, ?_, ?_⟩
  · by_contra hz
    push Not at hz
    have hre0 : q.re = 0 := by exact_mod_cast (div_eq_zero_iff.mp hz.1).resolve_right hLQ
    have him0 : q.im = 0 := by exact_mod_cast (div_eq_zero_iff.mp hz.2).resolve_right hLQ
    apply hq
    exact Zsqrtd.ext hre0 him0
  · have h : (a : ℚ) = m * ((q.re : ℚ) ^ 2 - (q.im : ℚ) ^ 2) := by exact_mod_cast hre
    rw [h]
    field_simp
  · have h : (b : ℚ) = m * (2 * (q.re : ℚ) * q.im) := by exact_mod_cast him
    rw [h]
    field_simp

namespace IntegralModel

/-- The canonical positive squarefree content attached to a labelled corner. -/
noncomputable def cornerClass (M : IntegralModel) (c : Bool × Bool) : ℕ :=
  squarefreePart (M.cornerContent c)

/-- The four root equations for the original signed displacements. -/
theorem corner_gaussian_root (M : IntegralModel) (hX : Odd M.X) (hL : Even M.L)
    (c : Bool × Bool) :
    ∃ q : GaussianInt, q ≠ 0 ∧
      (⟨M.cornerX c.1, M.cornerY c.2⟩ : GaussianInt) =
        (M.cornerClass c : GaussianInt) * q ^ 2 ∧
      M.cornerRadius c = (M.cornerClass c : ℤ) * Zsqrtd.norm q ∧
      0 < Zsqrtd.norm q := by
  apply canonical_gaussian_square
  · unfold PythagoreanTriple
    nlinarith [M.corner_sq c]
  · exact Int.odd_iff.mp (M.cornerX_odd hX hL c.1)
  · exact M.cornerRadius_pos c

theorem cornerClass_pos (M : IntegralModel) (c : Bool × Bool) :
    0 < M.cornerClass c := squarefreePart_pos _

theorem cornerClass_squarefree (M : IntegralModel) (c : Bool × Bool) :
    Squarefree (M.cornerClass c) := squarefreePart_squarefree _

theorem cornerClass_odd (M : IntegralModel) (hX : Odd M.X) (hL : Even M.L)
    (c : Bool × Bool) : Odd (M.cornerClass c) :=
  squarefreePart_odd (M.cornerContent_odd hX hL c)

theorem cornerClass_coprime_side (M : IntegralModel) (c : Bool × Bool) :
    Nat.Coprime (M.cornerClass c) M.L.natAbs :=
  squarefreePart_coprime_left (M.cornerContent_coprime_side c)

theorem cornerClass_pairwise_coprime (M : IntegralModel) {c c' : Bool × Bool}
    (hne : c ≠ c') : Nat.Coprime (M.cornerClass c) (M.cornerClass c') :=
  squarefreePart_coprime (M.cornerContent_pairwise_coprime hne)

/-- Each actual corner content has the required prime support, proved through
its divisibility into the original diagonal product. -/
theorem cornerContent_prime_support (M : IntegralModel)
    (hL : (2 : ℤ) ∣ M.L) (hXY : M.X % 2 ≠ M.Y % 2)
    (c : Bool × Bool) {p : ℕ} (hp : p.Prime) (hd : p ∣ M.cornerContent c) :
    p % 8 = 1 ∨ p % 8 = 7 :=
  M.prime_dvd_diagonal_product hL hXY hp
    (dvd_trans (Int.natCast_dvd_natCast.mpr hd) (M.cornerContent_dvd_diagonal_product c))

theorem cornerClass_prime_support (M : IntegralModel)
    (hL : (2 : ℤ) ∣ M.L) (hXY : M.X % 2 ≠ M.Y % 2)
    (c : Bool × Bool) {p : ℕ} (hp : p.Prime) (hd : p ∣ M.cornerClass c) :
    p % 8 = 1 ∨ p % 8 = 7 :=
  M.cornerContent_prime_support hL hXY c hp (dvd_trans hd (squarefreePart_dvd _))

/-- Full canonical squareclass identity for each original labelled corner. -/
theorem corner_gaussian_squareclass (M : IntegralModel) (hX : Odd M.X) (hL : Even M.L)
    (c : Bool × Bool) :
    GaussianRationalSquareClass ((M.cornerX c.1 : ℚ) / M.L)
      ((M.cornerY c.2 : ℚ) / M.L) ((M.L : ℚ) * M.cornerClass c) := by
  obtain ⟨q, hq, hroot, _, _⟩ := M.corner_gaussian_root hX hL c
  exact gaussian_squareclass_denominator (ne_of_gt M.L_pos) (M.cornerClass_pos c) hq hroot

/-- The norm formula in the literal division form used in the manuscript. -/
theorem corner_gaussian_root_norm_div (M : IntegralModel) (hX : Odd M.X)
    (c : Bool × Bool) :
    ∃ q : GaussianInt, q ≠ 0 ∧
      (⟨M.cornerX c.1, M.cornerY c.2⟩ : GaussianInt) =
        (M.cornerClass c : GaussianInt) * q ^ 2 ∧
      Zsqrtd.norm q = M.cornerRadius c / (M.cornerClass c : ℤ) ∧
      0 < Zsqrtd.norm q := by
  have hL : Even M.L := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  obtain ⟨q, hq, hroot, hnorm, hnpos⟩ := M.corner_gaussian_root hX hL c
  have hm : (M.cornerClass c : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (M.cornerClass_pos c))
  refine ⟨q, hq, hroot, ?_, hnpos⟩
  rw [hnorm, Int.mul_ediv_cancel_left _ hm]

/-- Same squareclass statement in the unit-square coordinates, with every
corner translation still explicit. -/
theorem corner_gaussian_squareclass_coordinates (M : IntegralModel) (hX : Odd M.X)
    (c : Bool × Bool) :
    GaussianRationalSquareClass ((M.X : ℚ) / M.L - if c.1 then 1 else 0)
      ((M.Y : ℚ) / M.L - if c.2 then 1 else 0) ((M.L : ℚ) * M.cornerClass c) := by
  have hL : Even M.L := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  have h := M.corner_gaussian_squareclass hX hL c
  have hLn : (M.L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt M.L_pos)
  have hx : (M.cornerX c.1 : ℚ) / M.L = (M.X : ℚ) / M.L - if c.1 then 1 else 0 := by
    cases hc : c.1 <;> simp [cornerX, sub_div, hLn]
  have hy : (M.cornerY c.2 : ℚ) / M.L = (M.Y : ℚ) / M.L - if c.2 then 1 else 0 := by
    cases hc : c.2 <;> simp [cornerY, sub_div, hLn]
  rwa [hx, hy] at h

/-- Manuscript theorem `int:gaussian`, forward direction with the prescribed
horizontal-odd orientation. Every datum is derived from the original four
integer squared-distance identities and joint primitivity. -/
theorem canonical_corner_classes (M : IntegralModel) (hX : Odd M.X) :
    (∀ c, Odd (M.cornerContent c) ∧ Nat.Coprime (M.cornerContent c) M.L.natAbs) ∧
    (∀ c c', c ≠ c' → Nat.Coprime (M.cornerContent c) (M.cornerContent c')) ∧
    (∀ c p, p.Prime → p ∣ M.cornerContent c → p % 8 = 1 ∨ p % 8 = 7) ∧
    (∀ c, 0 < M.cornerClass c ∧ Odd (M.cornerClass c) ∧ Squarefree (M.cornerClass c)) ∧
    (∀ c c', c ≠ c' → Nat.Coprime (M.cornerClass c) (M.cornerClass c')) ∧
    (∀ c, ∃ q : GaussianInt, q ≠ 0 ∧
      (⟨M.cornerX c.1, M.cornerY c.2⟩ : GaussianInt) =
        (M.cornerClass c : GaussianInt) * q ^ 2 ∧
      M.cornerRadius c = (M.cornerClass c : ℤ) * Zsqrtd.norm q ∧
      0 < Zsqrtd.norm q) ∧
    (∀ c, GaussianRationalSquareClass ((M.cornerX c.1 : ℚ) / M.L)
      ((M.cornerY c.2 : ℚ) / M.L) ((M.L : ℚ) * M.cornerClass c)) := by
  obtain ⟨hl, hxy⟩ := M.basic_mod_four
  have hLd : (2 : ℤ) ∣ M.L := Int.dvd_of_emod_eq_zero hl
  have hLe : Even M.L := even_iff_two_dvd.mpr hLd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact ⟨M.cornerContent_odd hX hLe c, M.cornerContent_coprime_side c⟩
  · intro c c' hne
    exact M.cornerContent_pairwise_coprime hne
  · intro c p hp hd
    exact M.cornerContent_prime_support hLd (by omega) c hp hd
  · intro c
    exact ⟨M.cornerClass_pos c, M.cornerClass_odd hX hLe c, M.cornerClass_squarefree c⟩
  · intro c c' hne
    exact M.cornerClass_pairwise_coprime hne
  · exact M.corner_gaussian_root hX hLe
  · exact M.corner_gaussian_squareclass hX hLe

end IntegralModel

end FourCorner

#print axioms FourCorner.primitive_gaussian_square
#print axioms FourCorner.gaussian_square_after_content

#print axioms FourCorner.canonical_gaussian_square

#print axioms FourCorner.IntegralModel.corner_gaussian_root
#print axioms FourCorner.IntegralModel.cornerContent_prime_support
#print axioms FourCorner.IntegralModel.cornerClass_prime_support

#print axioms FourCorner.gaussian_squareclass_denominator
#print axioms FourCorner.IntegralModel.corner_gaussian_squareclass

#print axioms FourCorner.IntegralModel.canonical_corner_classes

#print axioms FourCorner.IntegralModel.corner_gaussian_root_norm_div
#print axioms FourCorner.IntegralModel.corner_gaussian_squareclass_coordinates
