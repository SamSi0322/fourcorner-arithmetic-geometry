import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Prime

/-!
Pure Noetherian induction for cancellation in extended ideals.
This is a conditional algebraic core: its two hypotheses must be established
from flatness and fibre regularity before applying it to a geometric theorem.
Neither the source nor target ring is assumed nontrivial.
-/
namespace FourCorner.IdealInduction

universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The elementary direction of principal-colon transport, requiring no flatness. -/
theorem map_colon_singleton_le (I : Ideal A) (a : A) :
    (I.colon ({a} : Set A)).map (algebraMap A B) ≤
      (I.map (algebraMap A B)).colon ({algebraMap A B a} : Set B) := by
  rw [Ideal.map_le_iff_le_comap]
  intro z hz
  change algebraMap A B z ∈ (I.map (algebraMap A B)).colon {algebraMap A B a}
  rw [Submodule.mem_colon_singleton]
  change algebraMap A B z * algebraMap A B a ∈ I.map (algebraMap A B)
  rw [← map_mul]
  exact Ideal.mem_map_of_mem (algebraMap A B) (by simpa using hz)

/-- If principal colons extend correctly and cancellation holds over every prime
ideal, Noetherian ideal induction gives cancellation over every ideal.

At a proper nonprime ideal `I`, use `a,b ∉ I` with `a*b ∈ I`; apply induction
first at `I + (a)` and then at `(I:a)`, both strictly greater than `I`.
The explicit top branch also handles zero rings. -/
theorem all_ideal_cancellation [IsNoetherianRing A] (g : B)
    (primeCancellation : ∀ (p : Ideal A), p.IsPrime → ∀ (x : B),
      g * x ∈ p.map (algebraMap A B) → x ∈ p.map (algebraMap A B))
    (colonTransport : ∀ (I : Ideal A) (a : A) (y : B),
      algebraMap A B a * y ∈ I.map (algebraMap A B) →
        y ∈ (I.colon ({a} : Set A)).map (algebraMap A B)) :
    ∀ (I : Ideal A) (x : B),
      g * x ∈ I.map (algebraMap A B) → x ∈ I.map (algebraMap A B) := by
  classical
  intro I
  refine IsNoetherian.induction
    (P := fun I : Ideal A => ∀ x : B,
      g * x ∈ I.map (algebraMap A B) → x ∈ I.map (algebraMap A B))
    (fun (I : Ideal A) ih => ?_) I
  by_cases htop : I = ⊤
  · subst I
    intro x _
    rw [Ideal.map_top]
    exact Submodule.mem_top
  by_cases hp : I.IsPrime
  · exact primeCancellation I hp
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Ideal.not_isPrime_iff.mp hp).resolve_left htop
  let J : Ideal A := I ⊔ Ideal.span ({a} : Set A)
  let K : Ideal A := I.colon ({a} : Set A)
  have hIJ : I < J := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    exact ha (heq.symm ▸ (show a ∈ J from
      (show Ideal.span {a} ≤ J from le_sup_right) (Ideal.mem_span_singleton_self a)))
  have hIK : I < K := by
    refine lt_of_le_of_ne Ideal.le_colon ?_
    intro heq
    have hbK : b ∈ K := by
      change b ∈ I.colon {a}
      simpa [Submodule.mem_colon_singleton, mul_comm] using hab
    exact hb (heq.symm ▸ hbK)
  intro x hx
  have hxJ := ih J hIJ x (Ideal.map_mono le_sup_left hx)
  change x ∈ (I ⊔ Ideal.span ({a} : Set A)).map (algebraMap A B) at hxJ
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton] at hxJ
  obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hxJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hw
  have hxy : z + y * algebraMap A B a = x := by simpa [hy] using hzw
  have hgyz : g * z ∈ I.map (algebraMap A B) := Ideal.mul_mem_left _ g hz
  have hprod : algebraMap A B a * (g * y) ∈ I.map (algebraMap A B) := by
    have hsub := (I.map (algebraMap A B)).sub_mem hx hgyz
    have heq : g * x - g * z = algebraMap A B a * (g * y) := by
      rw [← hxy, mul_add, add_sub_cancel_left]
      ac_rfl
    rwa [heq] at hsub
  have hgyK : g * y ∈ K.map (algebraMap A B) := colonTransport I a (g * y) hprod
  have hyK : y ∈ K.map (algebraMap A B) := ih K hIK y hgyK
  have hya := map_colon_singleton_le (B := B) I a hyK
  rw [Submodule.mem_colon_singleton] at hya
  change y * algebraMap A B a ∈ I.map (algebraMap A B) at hya
  rw [← hxy]
  exact (I.map (algebraMap A B)).add_mem hz hya

end FourCorner.IdealInduction
