import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Actual quadratic algebra K[√2] norm witnesses, valid over every characteristic-zero field.
The remaining local-global and valuation theorems are deliberately not asserted here. -/
namespace FourCorner.HasseNormWitness
variable {K : Type*} [Field K] [CharZero K]
abbrev SqrtTwo (K : Type*) [CommRing K] := QuadraticAlgebra K 2 0

def pWitness (z v t : K) : SqrtTwo K :=
  ⟨(-v+2*t)/(2*z), (v-t)/(2*z)⟩
def abWitness (b w t z : K) : SqrtTwo K :=
  ⟨b/w*(2*t+2*z), b/w*(t+2*z)⟩

theorem pWitness_norm (p z v t : K) (hz : z ≠ 0)
    (h : v^2 = 2*t^2-4*p*z^2) :
    (pWitness z v t).norm = p := by
  simp only [pWitness, QuadraticAlgebra.norm_def]
  field_simp
  linear_combination -h

theorem abWitness_norm (p z w t : K) (hw : w ≠ 0)
    (h : (p-1)*w^2 = 2*(p+1)*(t^2-2*z^2)) :
    (abWitness (p+1) w t z).norm = (p-1)*(p+1) := by
  simp only [abWitness, QuadraticAlgebra.norm_def]
  field_simp
  linear_combination -(p+1)*h

/-- The two displayed witnesses are norms in the actual rank-two algebra,
not mere labels for a norm predicate. -/
theorem omission_norm_witnesses (p z v w t : K) (hz : z ≠ 0) (hw : w ≠ 0)
    (hv : v^2 = 2*t^2-4*p*z^2)
    (ht : (p-1)*w^2 = 2*(p+1)*(t^2-2*z^2)) :
    (∃ x : SqrtTwo K, x.norm = p) ∧
    (∃ x : SqrtTwo K, x.norm = (p-1)*(p+1)) :=
  ⟨⟨pWitness z v t, pWitness_norm p z v t hz hv⟩,
   ⟨abWitness (p+1) w t z, abWitness_norm p z w t hw ht⟩⟩

/-- Nonzero projective omission points over a field where 2 is nonsquare
cannot have z=0 or w=0. This includes the omitted boundary points. -/
theorem omission_denominators (p z v w t : K) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (h2 : ¬ IsSquare (2 : K))
    (hnonzero : ¬ (z=0 ∧ v=0 ∧ w=0 ∧ t=0))
    (hv : v^2 = 2*t^2-4*p*z^2)
    (ht : (p-1)*w^2 = 2*(p+1)*(t^2-2*z^2)) :
    z ≠ 0 ∧ w ≠ 0 := by
  have anisotropic : ∀ x y : K, x^2 = 2*y^2 → y=0 := by
    intro x y h
    by_contra hy
    apply h2
    refine ⟨x/y, ?_⟩
    field_simp
    linear_combination -h
  have hz : z ≠ 0 := by
    intro hz
    have ht0 : t=0 := anisotropic v t (by simpa [hz] using hv)
    have hv0 : v=0 := by
      have hh : v^2=0 := by simpa [hz,ht0] using hv
      exact (sq_eq_zero_iff).mp hh
    have hw0 : w=0 := by
      have hh : (p-1)*w^2=0 := by simpa [hz,ht0] using ht
      exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hh).resolve_left ha)
    exact hnonzero ⟨hz,hv0,hw0,ht0⟩
  refine ⟨hz, ?_⟩
  intro hw
  have hh : t^2=2*z^2 := by
    have he : 2*(p+1)*(t^2-2*z^2)=0 := by simpa [hw] using ht.symm
    have he' := (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hb)
    exact sub_eq_zero.mp he'
  exact hz (anisotropic t z hh)

/-- At a split place every scalar is an actual norm, with an explicit witness. -/
theorem norm_surjective_of_two_square (e : K) (he : e^2 = 2) (c : K) :
    ∃ x : SqrtTwo K, x.norm = c := by
  have he0 : e ≠ 0 := by
    intro hz
    simp [hz] at he
  refine ⟨⟨(c+1)/2, (c-1)/(2*e)⟩, ?_⟩
  simp only [QuadraticAlgebra.norm_def]
  field_simp
  linear_combination (c-1)^2*he

/-- A genuine nonzero full-source point supplies the two local norms.
All five homogeneous coordinates are admitted, including Z=0 a priori. -/
theorem full_source_local_norms (p Z U V W T : K)
    (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (h0 : ¬ (Z=0 ∧ U=0 ∧ V=0 ∧ W=0 ∧ T=0))
    (hV : p*V^2=2*(p-1)*(U^2-p*Z^2))
    (hW : p*W^2=2*(p+1)*(U^2+p*Z^2))
    (hT : p*T^2=(p-1)*U^2+p*(p+1)*Z^2) :
    (∃ x : SqrtTwo K, x.norm=p) ∧
    (∃ x : SqrtTwo K, x.norm=(p-1)*(p+1)) := by
  by_cases h2 : IsSquare (2 : K)
  · obtain ⟨e,he⟩ := h2
    have he' : e^2=2 := by simpa [pow_two] using he.symm
    exact ⟨norm_surjective_of_two_square e he' p,
      norm_surjective_of_two_square e he' ((p-1)*(p+1))⟩
  · have hv : V^2=2*T^2-4*p*Z^2 := by
      apply mul_left_cancel₀ hp
      linear_combination hV - 2*hT
    have ht : (p-1)*W^2=2*(p+1)*(T^2-2*Z^2) := by
      apply mul_left_cancel₀ hp
      linear_combination (p-1)*hW - 2*(p+1)*hT
    have hnon : ¬ (Z=0 ∧ V=0 ∧ W=0 ∧ T=0) := by
      rintro ⟨hz,hv0,hw,ht0⟩
      have hu : U=0 := by
        have hh : (p-1)*U^2=0 := by simpa [hz,ht0] using hT.symm
        exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left ha)
      exact h0 ⟨hz,hu,hv0,hw,ht0⟩
    obtain ⟨hz,hw⟩ := omission_denominators p Z V W T ha hb h2 hnon hv ht
    exact omission_norm_witnesses p Z V W T hz hw hv ht

/-- Actual norm witnesses are closed under division by a nonzero norm. -/
theorem exists_norm_div {a b : K} (hb : b ≠ 0)
    (haN : ∃ x : SqrtTwo K, x.norm=a) (hbN : ∃ y : SqrtTwo K, y.norm=b) :
    ∃ z : SqrtTwo K, z.norm=a/b := by
  obtain ⟨x,hx⟩ := haN
  obtain ⟨y,hy⟩ := hbN
  refine ⟨x * star y * algebraMap K (SqrtTwo K) (1/b), ?_⟩
  simp only [map_mul, QuadraticAlgebra.norm_star, QuadraticAlgebra.norm_algebraMap,hx,hy]
  field_simp

theorem exists_norm_neg {a : K} (h : ∃ x : SqrtTwo K, x.norm=a) :
    ∃ x : SqrtTwo K, x.norm= -a := by
  obtain ⟨x,hx⟩ := h
  refine ⟨(⟨1,1⟩ : SqrtTwo K)*x, ?_⟩
  rw [map_mul,hx]
  have hh : (⟨1,1⟩ : SqrtTwo K).norm = -1 := by
    norm_num [QuadraticAlgebra.norm_def]
  rw [hh]
  ring

#print axioms exists_norm_div
#print axioms exists_norm_neg
#print axioms full_source_local_norms
#print axioms norm_surjective_of_two_square
#print axioms omission_denominators

#print axioms pWitness_norm
#print axioms abWitness_norm
#print axioms omission_norm_witnesses
end FourCorner.HasseNormWitness
