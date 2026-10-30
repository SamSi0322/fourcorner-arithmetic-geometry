import NativeBinaryP1

noncomputable section
set_option autoImplicit false
namespace FourCorner.BinaryQuarticDoubleRoots
open Polynomial
variable {K : Type*} [Field K]

/-- An actual binary homogeneous quadratic with its original coefficients. -/
def quadratic (a b d : K) : Binary K :=
  MvPolynomial.C a * MvPolynomial.X 0^2 +
  MvPolynomial.C b * MvPolynomial.X 0 * MvPolynomial.X 1 +
  MvPolynomial.C d * MvPolynomial.X 1^2

theorem quadratic_homogeneous (a b d : K) : (quadratic a b d).IsHomogeneous 2 := by
  have h0 := MvPolynomial.isHomogeneous_X (R := K) (0 : Fin 2)
  have h1 := MvPolynomial.isHomogeneous_X (R := K) (1 : Fin 2)
  exact (((MvPolynomial.isHomogeneous_X_pow 0 2).C_mul a).add
    ((h0.C_mul b).mul h1)).add ((MvPolynomial.isHomogeneous_X_pow 1 2).C_mul d)

theorem scaled_square_homogeneous (c a b d : K) :
    (MvPolynomial.C c * (quadratic a b d)^2).IsHomogeneous 4 := by
  exact ((quadratic_homogeneous a b d).pow 2).C_mul c

theorem dehom_quadratic (a b d : K) :
    dehom (quadratic a b d) = C a * X^2 + C b * X + C d := by
  simp [dehom, quadratic]

theorem dehom_scaled_square (c a b d : K) :
    dehom (MvPolynomial.C c * (quadratic a b d)^2) =
      C c * (C a * X^2 + C b * X + C d)^2 := by
  calc
    dehom (MvPolynomial.C c * (quadratic a b d)^2) =
        dehom (MvPolynomial.C c) * (dehom (quadratic a b d))^2 := by
          unfold dehom
          rw [map_mul, map_pow]
    _ = C c * (C a * X^2 + C b * X + C d)^2 := by
      rw [dehom_quadratic]
      simp [dehom]

private theorem finite_root_data {F : Binary K} (u : K) (h : ZeroJet F ![u, 1]) :
    (dehom F).eval u = 0 ∧ (dehom F).derivative.eval u = 0 := by
  refine ⟨(dehom_eval F u).trans h.1, ?_⟩
  rw [derivative_dehom, dehom_eval]
  exact h.2 0

theorem eval_infinity_homogenize_four (p : K[X]) :
    MvPolynomial.aeval (![1, 0] : Fin 2 → K) (p.homogenize 4) = p.coeff 4 := by
  rw [homogenize_four]
  simp

theorem partial_one_infinity_homogenize_four (p : K[X]) :
    MvPolynomial.aeval (![1, 0] : Fin 2 → K) (MvPolynomial.pderiv 1 (p.homogenize 4)) = p.coeff 3 := by
  rw [homogenize_four]
  simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X,
    Pi.single_apply]

theorem infinity_coefficients {F : Binary K} (hF : F.IsHomogeneous 4)
    (h : ZeroJet F ![1, 0]) : (dehom F).coeff 4 = 0 ∧ (dehom F).coeff 3 = 0 := by
  constructor
  · have hz : MvPolynomial.aeval (![1, 0] : Fin 2 → K) ((dehom F).homogenize 4) = 0 := by
      rw [recover F hF]
      exact h.1
    rwa [eval_infinity_homogenize_four] at hz
  · have hz : MvPolynomial.aeval (![1, 0] : Fin 2 → K) (MvPolynomial.pderiv 1 ((dehom F).homogenize 4)) = 0 := by
      rw [recover F hF]
      exact h.2 1
    rwa [partial_one_infinity_homogenize_four] at hz

theorem dehom_degree_of_infinity {F : Binary K} (hF : F.IsHomogeneous 4)
    (h : ZeroJet F ![1, 0]) : (dehom F).natDegree ≤ 2 := by
  have hh := infinity_coefficients hF h
  have hdeg := dehom_degree hF
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases h4 : k ≤ 4
  · have h34 : k = 3 ∨ k = 4 := by omega
    rcases h34 with rfl | rfl
    · exact hh.2
    · exact hh.1
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

private theorem finite_finite_square {F : Binary K} (hF : F.IsHomogeneous 4) (hf : F ≠ 0)
    (u v : K) (huv : u ≠ v) (hu : ZeroJet F ![u, 1]) (hv : ZeroJet F ![v, 1]) :
    ∃ c a b d : K, c ≠ 0 ∧ b^2 - 4*a*d ≠ 0 ∧
      F = MvPolynomial.C c * (quadratic a b d)^2 := by
  obtain ⟨hu0, hu1⟩ := finite_root_data u hu
  obtain ⟨hv0, hv1⟩ := finite_root_data v hv
  obtain ⟨c, hc, he⟩ := two_double_roots (dehom_ne_zero hF hf) (dehom_degree hF)
    u v huv hu0 hu1 hv0 hv1
  refine ⟨c, 1, -(u+v), u*v, hc, ?_, ?_⟩
  · have hh : (u-v)^2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr huv)
    convert hh using 1 <;> ring
  · apply dehom_injective hF (scaled_square_homogeneous c 1 (-(u+v)) (u*v))
    calc
      dehom F = C c * ((X-C u)*(X-C v))^2 := he
      _ = dehom (MvPolynomial.C c * (quadratic 1 (-(u+v)) (u*v))^2) := by
        rw [dehom_scaled_square]
        simp only [map_one, map_neg, map_add, map_mul]
        ring

private theorem infinity_finite_square {F : Binary K} (hF : F.IsHomogeneous 4) (hf : F ≠ 0)
    (u : K) (hi : ZeroJet F ![1, 0]) (hu : ZeroJet F ![u, 1]) :
    ∃ c a b d : K, c ≠ 0 ∧ b^2 - 4*a*d ≠ 0 ∧
      F = MvPolynomial.C c * (quadratic a b d)^2 := by
  obtain ⟨hu0, hu1⟩ := finite_root_data u hu
  obtain ⟨c, hc, he⟩ := one_double_root (dehom_ne_zero hF hf)
    (dehom_degree_of_infinity hF hi) u hu0 hu1
  refine ⟨c, 0, 1, -u, hc, by simp, ?_⟩
  apply dehom_injective hF (scaled_square_homogeneous c 0 1 (-u))
  calc
    dehom F = C c * (X-C u)^2 := he
    _ = dehom (MvPolynomial.C c * (quadratic 0 1 (-u))^2) := by
      rw [dehom_scaled_square]
      simp only [map_zero, map_one, map_neg]
      ring

/-- Two distinct ACTUAL native P1 points at which a nonzero homogeneous quartic and
both formal partials vanish force a scalar square with NONZERO discriminant.
All native points, infinity and all representative scalings are retained. -/
theorem two_distinct_double_points {F : Binary K} (hF : F.IsHomogeneous 4) (hf : F ≠ 0)
    (P Q : P1 K) (hPQ : P ≠ Q) (hP : DoubleAt F P) (hQ : DoubleAt F Q) :
    ∃ c a b d : K, c ≠ 0 ∧ b^2 - 4*a*d ≠ 0 ∧
      F = MvPolynomial.C c * (quadratic a b d)^2 := by
  rcases point_charts P with hPi | ⟨u, hPu⟩
  · subst P
    rcases point_charts Q with hQi | ⟨v, hQv⟩
    · exact (hPQ hQi.symm).elim
    · subst Q
      exact infinity_finite_square hF hf v ((doubleAt_infinity_iff hF).mp hP)
        ((doubleAt_finite_iff hF v).mp hQ)
  · subst P
    rcases point_charts Q with hQi | ⟨v, hQv⟩
    · subst Q
      exact infinity_finite_square hF hf u ((doubleAt_infinity_iff hF).mp hQ)
        ((doubleAt_finite_iff hF u).mp hP)
    · subst Q
      have huv : u ≠ v := fun h => hPQ (congrArg finitePoint h)
      exact finite_finite_square hF hf u v huv ((doubleAt_finite_iff hF u).mp hP)
        ((doubleAt_finite_iff hF v).mp hQ)

#print axioms two_distinct_double_points
end FourCorner.BinaryQuarticDoubleRoots
