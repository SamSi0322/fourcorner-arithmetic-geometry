import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
namespace FourCorner.BinaryQuarticDoubleRoots
open Polynomial
variable {K : Type*} [Field K]

/-- Vanishing of a polynomial and its formal derivative gives the actual double factor.
No characteristic or separability hypothesis is needed. -/
theorem linear_square_dvd {f : K[X]} (hf : f ≠ 0) (u : K)
    (hu : f.eval u = 0) (hdu : f.derivative.eval u = 0) :
    (X - C u)^2 ∣ f := by
  apply (le_rootMultiplicity_iff hf).mp
  have h : 1 < f.rootMultiplicity u :=
    (one_lt_rootMultiplicity_iff_isRoot hf).mpr ⟨hu, hdu⟩
  omega

/-- A nonzero polynomial with a full-degree divisor is a nonzero constant times it. -/
theorem scalar_of_dvd_degree {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (hdvd : g ∣ f) (hdeg : f.natDegree ≤ g.natDegree) :
    ∃ c : K, c ≠ 0 ∧ f = C c * g := by
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq; exact hf hq
  have hn : q.natDegree = 0 := by
    have hm := natDegree_mul hg hq0
    rw [← hq] at hm
    omega
  refine ⟨q.coeff 0, ?_, ?_⟩
  · intro h
    exact hq0 (by rw [eq_C_of_natDegree_eq_zero hn, h, map_zero])
  · calc
      f = g * q := hq
      _ = g * C (q.coeff 0) := congrArg (g * ·) (eq_C_of_natDegree_eq_zero hn)
      _ = C (q.coeff 0) * g := mul_comm _ _

/-- Two distinct double roots exhaust a nonzero polynomial of degree at most four. -/
theorem two_double_roots {f : K[X]} (hf : f ≠ 0) (hdeg : f.natDegree ≤ 4)
    (u v : K) (huv : u ≠ v)
    (hu : f.eval u = 0) (hdu : f.derivative.eval u = 0)
    (hv : f.eval v = 0) (hdv : f.derivative.eval v = 0) :
    ∃ c : K, c ≠ 0 ∧ f = C c * ((X - C u) * (X - C v))^2 := by
  have hc : IsCoprime (X - C u : K[X]) (X - C v) :=
    isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr huv))
  have hd := hc.pow.mul_dvd (linear_square_dvd hf u hu hdu)
    (linear_square_dvd hf v hv hdv)
  have h0 : ((X - C u) * (X - C v) : K[X])^2 ≠ 0 := by
    exact pow_ne_zero _ (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
  have hd' : ((X - C u) * (X - C v) : K[X])^2 ∣ f := by
    simpa only [mul_pow] using hd
  apply scalar_of_dvd_degree hf h0 hd'
  simpa [natDegree_pow, natDegree_mul (X_sub_C_ne_zero u) (X_sub_C_ne_zero v),
    natDegree_X_sub_C] using hdeg

/-- One finite double root exhausts a nonzero polynomial of degree at most two. -/
theorem one_double_root {f : K[X]} (hf : f ≠ 0) (hdeg : f.natDegree ≤ 2)
    (u : K) (hu : f.eval u = 0) (hdu : f.derivative.eval u = 0) :
    ∃ c : K, c ≠ 0 ∧ f = C c * (X - C u)^2 := by
  apply scalar_of_dvd_degree hf (pow_ne_zero _ (X_sub_C_ne_zero u))
    (linear_square_dvd hf u hu hdu)
  simpa [natDegree_pow, natDegree_X_sub_C] using hdeg

/-- A true multiplicity-at-least-four input, not merely two formal partials,
forces a fourth power under the actual degree bound. -/
theorem quadruple_root {f : K[X]} (hf : f ≠ 0) (hdeg : f.natDegree ≤ 4)
    (u : K) (hu : 4 ≤ f.rootMultiplicity u) :
    ∃ c : K, c ≠ 0 ∧ f = C c * (X - C u)^4 := by
  apply scalar_of_dvd_degree hf (pow_ne_zero _ (X_sub_C_ne_zero u))
    ((le_rootMultiplicity_iff hf).mp hu)
  simpa [natDegree_pow, natDegree_X_sub_C] using hdeg

#print axioms two_double_roots
#print axioms one_double_root
end FourCorner.BinaryQuarticDoubleRoots
