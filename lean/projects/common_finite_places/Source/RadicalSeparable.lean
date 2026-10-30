import ResidueGenerators
import Mathlib.FieldTheory.SeparableClosure

noncomputable section
namespace FourCorner.RadicalSeparable
open Polynomial IntermediateField
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- Characteristic different from two makes any actual quadratic root a
separable element, including the zero-root degeneracy. -/
theorem square_root {a : F} {r : E} (hroot : r^2 = algebraMap F E a)
    (h2 : (2:F) ≠ 0) : IsSeparable F r := by
  by_cases ha : a=0
  · have hr : r=0 := sq_eq_zero_iff.mp (by simpa [ha] using hroot)
    subst r
    simpa only [map_zero] using (isSeparable_algebraMap (F := F) (K := E) (0 : F))
  · exact (Polynomial.separable_X_pow_sub_C (n := 2) a (by simpa only [Nat.cast_ofNat] using h2) ha).of_dvd
      (minpoly.dvd F r (by simp [hroot]))

theorem generated {ι : Type*} (r : ι → E)
    (hgen : Algebra.adjoin F (Set.range r) = ⊤) (hsep : ∀ i, IsSeparable F (r i)) :
    Algebra.IsSeparable F E := by
  have h : Algebra.adjoin F (Set.range r) ≤ (separableClosure F E).toSubalgebra := by
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact hsep i
  rw [hgen] at h
  exact ⟨fun x => h (show x ∈ (⊤ : Subalgebra F E) by trivial)⟩

theorem primitive {a : F} {r : E} (hroot : r^2 = algebraMap F E a)
    (hgen : Algebra.adjoin F {r} = ⊤) (h2 : (2:F) ≠ 0) : Algebra.IsSeparable F E := by
  have hsep : IsSeparable F r := square_root hroot h2
  have h : Algebra.adjoin F {r} ≤ (separableClosure F E).toSubalgebra := by
    exact Algebra.adjoin_le (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hsep)
  rw [hgen] at h
  exact ⟨fun x => h (show x ∈ (⊤ : Subalgebra F E) by trivial)⟩

variable (K : Type*) [Field K] [NeZero (2:K)]
theorem four (t : K) : Algebra.IsSeparable (RatFunc K) (CommonLiteralField.field K t) :=
  generated (CommonLiteralField.root K t) (ResidueGenerators.four_root_generates K t)
    (fun i => square_root (CommonLiteralField.root_sq K t i) (ResidueRadicalDegree.two_ratFunc_ne_zero K))
theorem five (t κ : K) : Algebra.IsSeparable (RatFunc K) (CommonGenus17Field.field K t κ) :=
  generated (Genus17Geometry.fiveRoot t κ) (ResidueGenerators.fiveRoot_generates K t κ)
    (fun i => square_root (ResidueGenerators.fiveRoot_sq K t κ i) (ResidueRadicalDegree.two_ratFunc_ne_zero K))
end FourCorner.RadicalSeparable
#print axioms FourCorner.RadicalSeparable.square_root
#print axioms FourCorner.RadicalSeparable.four
#print axioms FourCorner.RadicalSeparable.five
