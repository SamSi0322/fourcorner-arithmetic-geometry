import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace FourCorner

open scoped QuadraticAlgebra

/-- Gaussian coordinates over a residue field. -/
abbrev GaussianMod (p : ℕ) := QuadraticAlgebra (ZMod p) (-1) 0

/-- The imaginary unit in Gaussian residue coordinates. -/
def gaussianModI (p : ℕ) : GaussianMod p := ⟨0, 1⟩

@[simp] lemma gaussianModI_sq (p : ℕ) : gaussianModI p ^ 2 = -1 := by
  ext <;> simp [gaussianModI, pow_two]

@[simp] lemma gaussianModI_pow_four (p : ℕ) : gaussianModI p ^ 4 = 1 := by
  rw [show (4:ℕ) = 2*2 by rfl, pow_mul, gaussianModI_sq]
  simp

lemma gaussianModI_pow_prime {p : ℕ} (hp4 : p % 4 = 3) :
    gaussianModI p ^ p = -gaussianModI p := by
  have he : p = 4 * (p / 4) + 3 := by omega
  rw [he, pow_add, pow_mul, gaussianModI_pow_four, one_pow, one_mul]
  rw [show (3:ℕ) = 2+1 by rfl, pow_add, gaussianModI_sq]
  simp

lemma gaussianMod_pow_prime {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (z : GaussianMod p) : z ^ p = star z := by
  let F := FiniteField.frobeniusAlgHom (ZMod p) (GaussianMod p)
  have hF (w : GaussianMod p) : F w = w ^ p := by
    simp [F, ZMod.card]
  have hz : z = algebraMap (ZMod p) (GaussianMod p) z.re +
      algebraMap (ZMod p) (GaussianMod p) z.im * gaussianModI p := by
    ext <;> simp [gaussianModI]
  rw [← hF, hz, map_add, map_mul]
  rw [F.commutes, F.commutes, hF, gaussianModI_pow_prime hp4]
  ext <;> simp [gaussianModI]

/-- For an inert prime, the `(p+1)`-st power is the Gaussian norm. -/
lemma gaussianMod_pow_prime_add_one {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (x y : ZMod p) :
    (⟨x,y⟩ : GaussianMod p) ^ (p+1) =
      algebraMap (ZMod p) (GaussianMod p) (x^2+y^2) := by
  rw [pow_add, gaussianMod_pow_prime hp4, pow_one]
  ext <;> simp [-map_pow] <;> ring

/-- The norm of a Gaussian square root is determined by the square. -/
lemma gaussianMod_square_half_pow {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (x y : ZMod p) :
    ((⟨x,y⟩ : GaussianMod p)^2)^((p+1)/2) =
      algebraMap (ZMod p) (GaussianMod p) (x^2+y^2) := by
  rw [← pow_mul, show 2*((p+1)/2) = p+1 by omega]
  exact gaussianMod_pow_prime_add_one hp4 x y

/-- A coordinate form of the norm/Frobenius bridge. -/
lemma gaussianMod_norm_of_square {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3)
    (x y a uRe uIm : ZMod p)
    (hRe : x^2-y^2 = a*uRe) (hIm : 2*x*y = a*uIm) :
    (algebraMap (ZMod p) (GaussianMod p) a * (⟨uRe,uIm⟩ : GaussianMod p))^((p+1)/2) =
      algebraMap (ZMod p) (GaussianMod p) (x^2+y^2) := by
  have hs : (⟨x,y⟩ : GaussianMod p)^2 =
      algebraMap (ZMod p) (GaussianMod p) a * (⟨uRe,uIm⟩ : GaussianMod p) := by
    ext <;> simp [pow_two]
    · linear_combination hRe
    · linear_combination hIm
  rw [← hs]
  exact gaussianMod_square_half_pow hp4 x y

end FourCorner
