import QuarticTwoDoublePoints
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section
set_option autoImplicit false
namespace FourCorner.BinaryQuarticDoubleRoots
open Polynomial
variable {K : Type*} [Field K]

/-- This uses the ACTUAL root multiset with multiplicities, not just a point count. -/
theorem polynomial_single_root [IsAlgClosed K] {f : K[X]} (hf : f ≠ 0)
    (u : K) (honly : ∀ z : K, f.eval z = 0 → z = u) :
    f = C f.leadingCoeff * (X-C u)^f.natDegree := by
  have hr : f.roots = Multiset.replicate f.roots.card u :=
    Multiset.eq_replicate_card.mpr (fun z hz => honly z ((mem_roots hf).mp hz))
  calc
    f = C f.leadingCoeff * (f.roots.map (X-C ·)).prod := (IsAlgClosed.splits f).eq_prod_roots
    _ = C f.leadingCoeff * (X-C u)^f.natDegree := by
      rw [hr]
      simp [IsAlgClosed.card_roots_eq_natDegree]

theorem polynomial_no_root_constant [IsAlgClosed K] {f : K[X]} (hf : f ≠ 0)
    (hno : ∀ z : K, f.eval z ≠ 0) : f = C (f.coeff 0) := by
  apply IsAlgClosed.roots_eq_zero_iff.mp
  exact Multiset.eq_zero_of_forall_notMem (fun z hz => hno z ((mem_roots hf).mp hz))

def linear (a b : K) : Binary K :=
  MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1

theorem linear_homogeneous (a b : K) : (linear a b).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X (R := K) (0 : Fin 2)).C_mul a).add
    ((MvPolynomial.isHomogeneous_X (R := K) (1 : Fin 2)).C_mul b)

theorem scaled_fourth_homogeneous (c a b : K) :
    (MvPolynomial.C c * (linear a b)^4).IsHomogeneous 4 :=
  ((linear_homogeneous a b).pow 4).C_mul c

theorem dehom_linear (a b : K) : dehom (linear a b) = C a * X + C b := by
  simp [dehom, linear]

theorem dehom_scaled_fourth (c a b : K) :
    dehom (MvPolynomial.C c * (linear a b)^4) = C c * (C a*X+C b)^4 := by
  calc
    dehom (MvPolynomial.C c * (linear a b)^4) = dehom (MvPolynomial.C c) * (dehom (linear a b))^4 := by
      unfold dehom
      rw [map_mul, map_pow]
    _ = C c * (C a*X+C b)^4 := by rw [dehom_linear]; simp [dehom]

/-- A real multiplicity-at-least-four input at a finite native chart root.
It is NOT inferred from vanishing of just the two first partials. -/
theorem finite_quadruple_fourth {F : Binary K} (hF : F.IsHomogeneous 4) (hf : F ≠ 0)
    (u : K) (hu : 4 ≤ (dehom F).rootMultiplicity u) :
    ∃ c : K, c ≠ 0 ∧ F = MvPolynomial.C c * (linear 1 (-u))^4 := by
  obtain ⟨c, hc, he⟩ := quadruple_root (dehom_ne_zero hF hf) (dehom_degree hF) u hu
  refine ⟨c, hc, ?_⟩
  apply dehom_injective hF (scaled_fourth_homogeneous c 1 (-u))
  calc
    dehom F = C c * (X-C u)^4 := he
    _ = dehom (MvPolynomial.C c * (linear 1 (-u))^4) := by
      rw [dehom_scaled_fourth]
      simp only [map_one, map_neg]
      ring

/-- Over an algebraically closed field a nonzero homogeneous quartic supported at
ONE actual native P1 zero is a nonzero scalar times a genuine linear fourth power.
The infinity-only case is retained. No partial-vanishing⇒quadruple assertion is used. -/
theorem singleton_projective_zero_fourth [IsAlgClosed K] {F : Binary K}
    (hF : F.IsHomogeneous 4) (hf : F ≠ 0) (P : P1 K)
    (honly : ∀ Q : P1 K, ZeroAt F Q → Q = P) :
    ∃ c a b : K, c ≠ 0 ∧ (a ≠ 0 ∨ b ≠ 0) ∧
      F = MvPolynomial.C c * (linear a b)^4 := by
  have hp0 := dehom_ne_zero hF hf
  rcases point_charts P with hPi | ⟨u, hPu⟩
  · subst P
    have hno : ∀ z : K, (dehom F).eval z ≠ 0 := by
      intro z hz
      have he : ZeroAt F (finitePoint z) := (zeroAt_finite_iff hF z).mpr
        ((dehom_eval F z).symm.trans hz)
      exact (infinity_ne_finite z) (honly _ he).symm
    have he := polynomial_no_root_constant hp0 hno
    have hc : (dehom F).coeff 0 ≠ 0 := by
      intro hz
      exact hp0 (by rw [he, hz, map_zero])
    refine ⟨(dehom F).coeff 0, 0, 1, hc, Or.inr one_ne_zero, ?_⟩
    have hh := recover F hF
    rw [he, homogenize_C] at hh
    simpa only [linear, map_zero, map_one, zero_mul, one_mul, zero_add] using hh.symm
  · subst P
    have h4 : (dehom F).coeff 4 ≠ 0 := by
      intro hz
      have he : ZeroAt F infinity := (zeroAt_infinity_iff hF).mpr (by
        rw [← recover F hF, eval_infinity_homogenize_four, hz])
      exact infinity_ne_finite u (honly _ he)
    have hdegree : (dehom F).natDegree = 4 :=
      Nat.le_antisymm (dehom_degree hF) (le_natDegree_of_ne_zero h4)
    have hroot : ∀ z : K, (dehom F).eval z = 0 → z = u := by
      intro z hz
      apply finitePoint_injective
      apply honly
      exact (zeroAt_finite_iff hF z).mpr ((dehom_eval F z).symm.trans hz)
    have he := polynomial_single_root hp0 u hroot
    rw [hdegree] at he
    refine ⟨(dehom F).leadingCoeff, 1, -u, leadingCoeff_ne_zero.mpr hp0, Or.inl one_ne_zero, ?_⟩
    apply dehom_injective hF (scaled_fourth_homogeneous _ 1 (-u))
    calc
      dehom F = C (dehom F).leadingCoeff * (X-C u)^4 := he
      _ = dehom (MvPolynomial.C (dehom F).leadingCoeff * (linear 1 (-u))^4) := by
        rw [dehom_scaled_fourth]
        simp only [map_one, map_neg]
        ring

/-- A literal nonzero homogeneous linear polynomial is retained in the singleton branch. -/
theorem singleton_projective_zero_linear_fourth [IsAlgClosed K] {F : Binary K}
    (hF : F.IsHomogeneous 4) (hf : F ≠ 0) (P : P1 K)
    (honly : ∀ Q : P1 K, ZeroAt F Q → Q = P) :
    ∃ (c : K) (L : Binary K), c ≠ 0 ∧ L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      F = MvPolynomial.C c * L^4 := by
  obtain ⟨c, a, b, hc, _, he⟩ := singleton_projective_zero_fourth hF hf P honly
  refine ⟨c, linear a b, hc, linear_homogeneous a b, ?_, he⟩
  intro hz
  rw [hz, zero_pow (by decide), mul_zero] at he
  exact hf he

/-- The singleton-support/hyperflex branch is a quadratic square with discriminant ZERO.
It is kept separate from the two-distinct-double-root nonzero-discriminant theorem. -/
theorem singleton_projective_zero_square [IsAlgClosed K] {F : Binary K}
    (hF : F.IsHomogeneous 4) (hf : F ≠ 0) (P : P1 K)
    (honly : ∀ Q : P1 K, ZeroAt F Q → Q = P) :
    ∃ c a b d : K, c ≠ 0 ∧ b^2 - 4*a*d = 0 ∧
      F = MvPolynomial.C c * (quadratic a b d)^2 := by
  obtain ⟨c, a, b, hc, _, he⟩ := singleton_projective_zero_fourth hF hf P honly
  refine ⟨c, a^2, 2*a*b, b^2, hc, by ring, ?_⟩
  have hq : (linear a b)^2 = quadratic (a^2) (2*a*b) (b^2) := by
    simp only [linear, quadratic, map_pow, map_mul, map_ofNat]
    ring
  rw [he, ← hq]
  ring

#print axioms singleton_projective_zero_fourth
#print axioms singleton_projective_zero_square
end FourCorner.BinaryQuarticDoubleRoots
