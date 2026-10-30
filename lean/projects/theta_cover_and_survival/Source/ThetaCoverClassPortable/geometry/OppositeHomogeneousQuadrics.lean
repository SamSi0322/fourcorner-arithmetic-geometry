import ThetaCoverClassPortable.geometry.OppositePolynomials
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
The actual projective quadrics for the opposite-source model, in the ordered
coordinates [P,Q,R,Z,T]. Homogeneity, the affine chart, and Jacobian statements
refer to these literal polynomials, not to an assumed smooth model.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.OppositeHomogeneousQuadrics
open OppositePolynomials
variable {K : Type*} [Field K] [CharZero K]

abbrev Ambient (K : Type*) [CommRing K] := MvPolynomial (Fin 5) K
abbrev AffineAmbient (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K

def F0 (mu nu : K) : Ambient K :=
  X 3 ^ 2 - C (A mu nu) * X 0 ^ 2 + C (2*A mu nu*nu^2) * X 4 ^ 2

def F1 (mu : K) : Ambient K :=
  X 1 ^ 2 - X 0 ^ 2 - C (mu^2)*X 4^2 - C 2*(X 3*X 4)

def F2 (mu : K) : Ambient K :=
  X 2 ^ 2 - X 0 ^ 2 - C (mu^2)*X 4^2 + C 2*(X 3*X 4)

def quadric (mu nu : K) : Fin 3 → Ambient K
  | 0 => F0 mu nu
  | 1 => F1 mu
  | 2 => F2 mu

def ideal (mu nu : K) : Ideal (Ambient K) := Ideal.span (Set.range (quadric mu nu))

theorem quadric_homogeneous (mu nu : K) (i : Fin 3) :
    (quadric mu nu i).IsHomogeneous 2 := by
  fin_cases i
  · exact ((isHomogeneous_X_pow _ _).sub (isHomogeneous_C_mul_X_pow _ _ _)).add
      (isHomogeneous_C_mul_X_pow _ _ _)
  · exact (((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).sub
      (isHomogeneous_C_mul_X_pow _ _ _)).sub
      (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).C_mul _)
  · exact (((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).sub
      (isHomogeneous_C_mul_X_pow _ _ _)).add
      (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).C_mul _)

theorem quadric_ne_zero (mu nu : K) (i : Fin 3) : quadric mu nu i ≠ 0 := by
  fin_cases i
  · intro hz
    have he := congrArg (MvPolynomial.eval (Pi.single 3 (1 : K))) hz
    simp [quadric, F0] at he
  · intro hz
    have he := congrArg (MvPolynomial.eval (Pi.single 1 (1 : K))) hz
    simp [quadric, F1] at he
  · intro hz
    have he := congrArg (MvPolynomial.eval (Pi.single 2 (1 : K))) hz
    simp [quadric, F2] at he

theorem quadric_totalDegree (mu nu : K) (i : Fin 3) : (quadric mu nu i).totalDegree = 2 :=
  (quadric_homogeneous mu nu i).totalDegree (quadric_ne_zero mu nu i)

theorem ideal_homogeneous (mu nu : K) :
    (ideal mu nu).IsHomogeneous (homogeneousSubmodule (Fin 5) K) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i,rfl⟩
  exact ⟨2, quadric_homogeneous mu nu i⟩

def homogeneousIdeal (mu nu : K) : HomogeneousIdeal (homogeneousSubmodule (Fin 5) K) :=
  ⟨ideal mu nu, ideal_homogeneous mu nu⟩

def affineEquation (mu nu : K) : Fin 3 → AffineAmbient K
  | 0 => X 3 ^ 2 - C (A mu nu)*X 0 ^ 2 + C (2*A mu nu*nu^2)
  | 1 => X 1 ^ 2 - X 0 ^ 2 - C (mu^2) - C 2*X 3
  | 2 => X 2 ^ 2 - X 0 ^ 2 - C (mu^2) + C 2*X 3

/-- Set T equal to one, preserving the four ordered affine coordinates. -/
def dehomT : Ambient K →+* AffineAmbient K :=
  eval₂Hom C ![X 0, X 1, X 2, X 3, 1]

theorem dehomT_quadric (mu nu : K) (i : Fin 3) :
    dehomT (quadric mu nu i) = affineEquation mu nu i := by
  fin_cases i <;> simp [dehomT, quadric, affineEquation, F0, F1, F2]

theorem dehomT_ideal (mu nu : K) :
    Ideal.map dehomT (ideal mu nu) = Ideal.span (Set.range (affineEquation mu nu)) := by
  rw [ideal, Ideal.map_span, ← Set.range_comp]
  have h : dehomT ∘ quadric mu nu = affineEquation mu nu := funext (dehomT_quadric mu nu)
  rw [h]

theorem affine_equations_iff (mu nu : K) (y : Fin 4 → K) :
    (∀ i : Fin 3, eval y (affineEquation mu nu i) = 0) ↔
    (y 3^2 = A mu nu*(y 0^2 - 2*nu^2) ∧
      y 1^2 = y 0^2 + mu^2 + 2*y 3 ∧ y 2^2 = y 0^2 + mu^2 - 2*y 3) := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [affineEquation, map_add, map_sub, map_pow, map_mul, eval_X, eval_C] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i <;>
      simp only [affineEquation, map_add, map_sub, map_pow, map_mul, eval_X, eval_C]
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2

def Solution (mu nu : K) (x : Fin 5 → K) : Prop :=
  ∀ i : Fin 3, eval x (quadric mu nu i) = 0

theorem solution_iff (mu nu : K) (x : Fin 5 → K) : Solution mu nu x ↔
    x 3^2 - A mu nu*x 0^2 + 2*A mu nu*nu^2*x 4^2 = 0 ∧
    x 1^2 - x 0^2 - mu^2*x 4^2 - 2*x 3*x 4 = 0 ∧
    x 2^2 - x 0^2 - mu^2*x 4^2 + 2*x 3*x 4 = 0 := by
  constructor
  · intro h
    exact ⟨by simpa [quadric, F0] using h 0,
      by simpa [quadric, F1, mul_assoc] using h 1, by simpa [quadric, F2, mul_assoc] using h 2⟩
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · simpa [quadric, F0] using h0
    · simpa [quadric, F1, mul_assoc] using h1
    · simpa [quadric, F2, mul_assoc] using h2

theorem infinity_relations {mu nu : K} {x : Fin 5 → K}
    (hx : Solution mu nu x) (hT : x 4 = 0) :
    x 3^2 = A mu nu*x 0^2 ∧ x 1^2 = x 0^2 ∧ x 2^2 = x 0^2 := by
  obtain ⟨h0,h1,h2⟩ := (solution_iff mu nu x).1 hx
  simp only [hT, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at h0 h1 h2
  exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

def jacobian (mu nu : K) (x : Fin 5 → K) : Matrix (Fin 3) (Fin 5) K :=
  fun i j => eval x (pderiv j (quadric mu nu i))

theorem jacobian_eq (mu nu : K) (x : Fin 5 → K) : jacobian mu nu x =
    !![-2*A mu nu*x 0, 0, 0, 2*x 3, 4*A mu nu*nu^2*x 4;
       -2*x 0, 2*x 1, 0, -2*x 4, -2*mu^2*x 4-2*x 3;
       -2*x 0, 0, 2*x 2, 2*x 4, -2*mu^2*x 4+2*x 3] := by
  have htwo : ∀ j : Fin 5, pderiv j (2 : Ambient K) = 0 := by
    intro j
    have ht : (2 : Ambient K) = C (2 : K) := by simp [map_ofNat]
    rw [ht, pderiv_C]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobian, quadric, F0, F1, F2, map_ofNat, htwo] <;> ring

def minor (mu nu : K) (x : Fin 5 → K) (cols : Fin 3 → Fin 5) : K :=
  ((jacobian mu nu x).submatrix id cols).det

theorem minor_PQR (mu nu : K) (x : Fin 5 → K) :
    minor mu nu x ![0,1,2] = -8*A mu nu*x 0*x 1*x 2 := by
  simp [minor, jacobian_eq, Matrix.det_fin_three, Matrix.submatrix]
  ring

theorem minor_ZQR (mu nu : K) (x : Fin 5 → K) :
    minor mu nu x ![3,1,2] = 8*x 3*x 1*x 2 := by
  simp [minor, jacobian_eq, Matrix.det_fin_three, Matrix.submatrix]
  ring

theorem minor_PZR (mu nu : K) (x : Fin 5 → K) :
    minor mu nu x ![0,3,2] = 8*x 0*x 2*(x 3+A mu nu*x 4) := by
  simp [minor, jacobian_eq, Matrix.det_fin_three, Matrix.submatrix]
  ring

theorem minor_PQZ (mu nu : K) (x : Fin 5 → K) :
    minor mu nu x ![0,1,3] = 8*x 0*x 1*(x 3-A mu nu*x 4) := by
  simp [minor, jacobian_eq, Matrix.det_fin_three, Matrix.submatrix]
  ring

namespace Scalar
variable {mu nu P Q R Z T : K}
variable (h0 : Z^2 - A mu nu * P^2 + 2*A mu nu*nu^2*T^2 = 0)
variable (h1 : Q^2 - P^2 - mu^2*T^2 - 2*Z*T = 0)
variable (h2 : R^2 - P^2 - mu^2*T^2 + 2*Z*T = 0)
variable (hn : ¬ (P=0 ∧ Q=0 ∧ R=0 ∧ Z=0 ∧ T=0))
include h0 h1 h2 hn

theorem nonzero_at_infinity (hT : T=0) : P ≠ 0 ∧ Q ≠ 0 ∧ R ≠ 0 := by
  have hp : P ≠ 0 := by
    intro hP
    have hzz : Z^2 = 0 := by simpa [hT, hP] using h0
    have hqq : Q^2 = 0 := by simpa [hT, hP] using h1
    have hrr : R^2 = 0 := by simpa [hT, hP] using h2
    exact hn ⟨hP, (by simpa using hqq), (by simpa using hrr), (by simpa using hzz), hT⟩
  refine ⟨hp, ?_, ?_⟩
  · intro hQ
    have hpp : P^2 = 0 := by simpa [hT, hQ] using h1
    exact hp ((by simpa using hpp))
  · intro hR
    have hpp : P^2 = 0 := by simpa [hT, hR] using h2
    exact hp ((by simpa using hpp))

theorem not_both_PQ_zero (hB : B mu nu ≠ 0) : ¬ (P=0 ∧ Q=0) := by
  rintro ⟨hP,hQ⟩
  have ht : T ≠ 0 := fun hT => (nonzero_at_infinity h0 h1 h2 hn hT).1 hP
  have hlinprod : T*(mu^2*T + 2*Z) = 0 := by
    rw [hP,hQ] at h1
    linear_combination -h1
  have hlin := (mul_eq_zero.mp hlinprod).resolve_left ht
  have hprod : (B mu nu)^2*T^2 = 0 := by
    rw [hP] at h0
    dsimp [A, B] at *
    linear_combination 4*h0 - (2*Z-mu^2*T)*hlin
  exact mul_ne_zero (pow_ne_zero _ hB) (pow_ne_zero _ ht) hprod

theorem not_both_PR_zero (hB : B mu nu ≠ 0) : ¬ (P=0 ∧ R=0) := by
  rintro ⟨hP,hR⟩
  have ht : T ≠ 0 := fun hT => (nonzero_at_infinity h0 h1 h2 hn hT).1 hP
  have hlinprod : T*(mu^2*T - 2*Z) = 0 := by
    rw [hP,hR] at h2
    linear_combination -h2
  have hlin := (mul_eq_zero.mp hlinprod).resolve_left ht
  have hprod : (B mu nu)^2*T^2 = 0 := by
    rw [hP] at h0
    dsimp [A, B] at *
    linear_combination 4*h0 + (2*Z+mu^2*T)*hlin
  exact mul_ne_zero (pow_ne_zero _ hB) (pow_ne_zero _ ht) hprod

theorem not_both_QR_zero (hA : A mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    ¬ (Q=0 ∧ R=0) := by
  rintro ⟨hQ,hR⟩
  have ht : T ≠ 0 := fun hT => (nonzero_at_infinity h0 h1 h2 hn hT).2.1 hQ
  have hzt : (4*T)*Z = 0 := by
    rw [hQ] at h1
    rw [hR] at h2
    linear_combination h2-h1
  have hz : Z = 0 := (mul_eq_zero.mp hzt).resolve_left (mul_ne_zero (by norm_num) ht)
  have hprod : A mu nu * S mu nu * T^2 = 0 := by
    rw [hQ,hz] at h1
    rw [hz] at h0
    dsimp [A,S] at *
    linear_combination h0 - (2*nu^2-mu^2)*h1
  exact mul_ne_zero (mul_ne_zero hA hS) (pow_ne_zero _ ht) hprod

theorem Pzero_Zne_zero (hA : A mu nu ≠ 0) (hnu : nu ≠ 0) (hP : P=0) : Z ≠ 0 := by
  intro hz
  have ht : T ≠ 0 := fun hT => (nonzero_at_infinity h0 h1 h2 hn hT).1 hP
  have hprod : 2*A mu nu*nu^2*T^2 = 0 := by simpa [hP,hz] using h0
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA)
    (pow_ne_zero _ hnu)) (pow_ne_zero _ ht) hprod

theorem Qzero_shift_ne_zero (hA : A mu nu ≠ 0) (hmu : mu ≠ 0) (hQ : Q=0) :
    Z + A mu nu*T ≠ 0 := by
  intro hz
  have ht : T ≠ 0 := fun hT => (nonzero_at_infinity h0 h1 h2 hn hT).2.1 hQ
  have hprod : 2*A mu nu*mu^2*T^2 = 0 := by
    rw [hQ] at h1
    dsimp [A] at *
    linear_combination h0 - (2*nu^2-mu^2)*h1 - (Z+(2*nu^2-mu^2)*T)*hz
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA)
    (pow_ne_zero _ hmu)) (pow_ne_zero _ ht) hprod

theorem Rzero_shift_ne_zero (hA : A mu nu ≠ 0) (hmu : mu ≠ 0) (hR : R=0) :
    Z - A mu nu*T ≠ 0 := by
  intro hz
  have ht : T ≠ 0 := fun hT => (nonzero_at_infinity h0 h1 h2 hn hT).2.2 hR
  have hprod : 2*A mu nu*mu^2*T^2 = 0 := by
    rw [hR] at h2
    dsimp [A] at *
    linear_combination h0 - (2*nu^2-mu^2)*h2 - (Z-(2*nu^2-mu^2)*T)*hz
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA)
    (pow_ne_zero _ hmu)) (pow_ne_zero _ ht) hprod

/-- The four scalar expressions are determinants of the PQR, ZQR, PZR,
and PQZ column minors of the actual homogeneous Jacobian (up to sign). -/
theorem nonzero_minor_alternative
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    -8*A mu nu*P*Q*R ≠ 0 ∨ 8*Z*Q*R ≠ 0 ∨
      8*P*R*(Z+A mu nu*T) ≠ 0 ∨ 8*P*Q*(Z-A mu nu*T) ≠ 0 := by
  by_cases hp : P=0
  · have hq : Q ≠ 0 := fun hq => not_both_PQ_zero h0 h1 h2 hn hB ⟨hp,hq⟩
    have hr : R ≠ 0 := fun hr => not_both_PR_zero h0 h1 h2 hn hB ⟨hp,hr⟩
    have hz := Pzero_Zne_zero h0 h1 h2 hn hA hnu hp
    exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz) hq) hr))
  by_cases hq : Q=0
  · have hr : R ≠ 0 := fun hr => not_both_QR_zero h0 h1 h2 hn hA hS ⟨hq,hr⟩
    have hz := Qzero_shift_ne_zero h0 h1 h2 hn hA hmu hq
    exact Or.inr (Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) hr) hz)))
  by_cases hr : R=0
  · have hz := Rzero_shift_ne_zero h0 h1 h2 hn hA hmu hr
    exact Or.inr (Or.inr (Or.inr (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) hq) hz)))
  exact Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hA) hp) hq) hr)

end Scalar

/-- A nonzero projective solution has an explicitly nonzero maximal minor
of the actual Jacobian, over any characteristic-zero field. -/
theorem exists_nonzero_minor {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    {x : Fin 5 → K} (hx : Solution mu nu x) (hxne : x ≠ 0) :
    ∃ cols : Fin 3 → Fin 5, minor mu nu x cols ≠ 0 := by
  obtain ⟨h0,h1,h2⟩ := (solution_iff mu nu x).1 hx
  have hn : ¬ (x 0=0 ∧ x 1=0 ∧ x 2=0 ∧ x 3=0 ∧ x 4=0) := by
    rintro ⟨hp,hq,hr,hz,ht⟩
    apply hxne
    funext i
    fin_cases i <;> simp_all
  rcases Scalar.nonzero_minor_alternative h0 h1 h2 hn hmu hnu hA hB hS with h | h | h | h
  · exact ⟨![0,1,2], by rwa [minor_PQR]⟩
  · exact ⟨![3,1,2], by rwa [minor_ZQR]⟩
  · exact ⟨![0,3,2], by rwa [minor_PZR]⟩
  · exact ⟨![0,1,3], by rwa [minor_PQZ]⟩

/-- The full rank follows from computed minors, without a nonsingularity
or smoothness hypothesis. This includes all nonzero solutions with T = 0. -/
theorem jacobian_rank {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    {x : Fin 5 → K} (hx : Solution mu nu x) (hxne : x ≠ 0) :
    (jacobian mu nu x).rank = 3 := by
  obtain ⟨cols,hcols⟩ := exists_nonzero_minor hmu hnu hA hB hS hx hxne
  have hr := Matrix.rank_of_det_ne_zero hcols
  have hle := Matrix.rank_submatrix_le (jacobian mu nu x) id cols
  rw [hr] at hle
  exact Nat.le_antisymm (by simpa using Matrix.rank_le_card_height (jacobian mu nu x))
    (by simpa using hle)

/-- Extending the coefficient field preserves the literal homogeneous forms. -/
theorem quadric_map {L : Type*} [Field L] [CharZero L] (phi : K →+* L)
    (mu nu : K) (i : Fin 3) :
    MvPolynomial.map phi (quadric mu nu i) = quadric (phi mu) (phi nu) i := by
  fin_cases i <;> simp [quadric, F0, F1, F2, A, map_ofNat]

/-- In particular every geometric point for an allowed rational ratio has
Jacobian rank three, including the genuine points at infinity. -/
theorem rational_jacobian_rank (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu/nu) (hlt : mu/nu < 2)
    {x : Fin 5 → K} (hx : Solution (algebraMap ℚ K mu) (algebraMap ℚ K nu) x)
    (hxne : x ≠ 0) : (jacobian (algebraMap ℚ K mu) (algebraMap ℚ K nu) x).rank = 3 := by
  have hmu : mu ≠ 0 := by intro hz; simp [hz] at hpos
  apply jacobian_rank ((map_ne_zero (algebraMap ℚ K)).2 hmu)
    ((map_ne_zero (algebraMap ℚ K)).2 hnu) ?_ ?_ ?_ hx hxne
  · simpa only [A_map] using (map_ne_zero (algebraMap ℚ K)).2 (rational_A_ne_zero mu nu hnu)
  · simpa only [B_map] using (map_ne_zero (algebraMap ℚ K)).2 (rational_B_ne_zero mu nu hnu hpos hlt)
  · simpa only [S_map] using (map_ne_zero (algebraMap ℚ K)).2 (rational_S_ne_zero mu nu hnu)

end FourCorner.OppositeHomogeneousQuadrics

#print axioms FourCorner.OppositeHomogeneousQuadrics.quadric_homogeneous
#print axioms FourCorner.OppositeHomogeneousQuadrics.quadric_ne_zero
#print axioms FourCorner.OppositeHomogeneousQuadrics.quadric_totalDegree
#print axioms FourCorner.OppositeHomogeneousQuadrics.ideal_homogeneous
#print axioms FourCorner.OppositeHomogeneousQuadrics.dehomT_quadric
#print axioms FourCorner.OppositeHomogeneousQuadrics.dehomT_ideal
#print axioms FourCorner.OppositeHomogeneousQuadrics.affine_equations_iff
#print axioms FourCorner.OppositeHomogeneousQuadrics.solution_iff
#print axioms FourCorner.OppositeHomogeneousQuadrics.infinity_relations
#print axioms FourCorner.OppositeHomogeneousQuadrics.jacobian_eq
#print axioms FourCorner.OppositeHomogeneousQuadrics.minor_PQR
#print axioms FourCorner.OppositeHomogeneousQuadrics.minor_ZQR
#print axioms FourCorner.OppositeHomogeneousQuadrics.minor_PZR
#print axioms FourCorner.OppositeHomogeneousQuadrics.minor_PQZ
#print axioms FourCorner.OppositeHomogeneousQuadrics.Scalar.nonzero_minor_alternative
#print axioms FourCorner.OppositeHomogeneousQuadrics.exists_nonzero_minor
#print axioms FourCorner.OppositeHomogeneousQuadrics.jacobian_rank
#print axioms FourCorner.OppositeHomogeneousQuadrics.quadric_map
#print axioms FourCorner.OppositeHomogeneousQuadrics.rational_jacobian_rank
