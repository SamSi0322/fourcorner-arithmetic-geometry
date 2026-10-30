import ThetaCoverClassPortable.geometry.MultiquadraticField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# The actual tower of three square-root adjunctions

All three fields are intermediate fields in one algebraic closure. The algebra
maps are the inclusions, and both the generators and the degrees are proved
from the concrete construction and squareclass independence.
-/

noncomputable section

namespace FourCorner.Multiquadratic.Tower

open IntermediateField

namespace Auxiliary

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem generator_top (K L : IntermediateField F E) (h : K ≤ L) (r : E)
    (hr : r ∈ L)
    (heq : L = (IntermediateField.adjoin K {r}).restrictScalars F)
    (ha : IsAlgebraic K r) :
    letI : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra
    Algebra.adjoin K ({⟨r, hr⟩} : Set L) = ⊤ := by
  let : Algebra K L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let J : IntermediateField K E := IntermediateField.extendScalars h
  have hJ : J = IntermediateField.adjoin K {r} := by
    apply IntermediateField.restrictScalars_injective F
    exact heq
  have hgen : IntermediateField.adjoin K ({⟨r, hr⟩} : Set J) = ⊤ := by
    apply IntermediateField.lift_injective J
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    exact hJ.symm
  have halg : IsAlgebraic K (⟨r, hr⟩ : J) :=
    (isAlgebraic_algHom_iff J.val J.val.injective).mp ha
  have hh := (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (by
    simpa using halg)).mp hgen
  exact hh

end Auxiliary

variable (F : Type*) [Field F]

def first (a : F) : IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.adjoin F {radical F a}

def second (a b : F) : IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.adjoin F {radical F a, radical F b}

abbrev third (a b c : F) : IntermediateField F (AlgebraicClosure F) := field F a b c

theorem first_le_second (a b : F) : first F a ≤ second F a b := by
  apply IntermediateField.adjoin.mono
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  simp [hx]

theorem second_le_third (a b c : F) : second F a b ≤ third F a b c := by
  apply IntermediateField.adjoin.mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem first_le_third (a b c : F) : first F a ≤ third F a b c :=
  (first_le_second F a b).trans (second_le_third F a b c)

instance algebra₁₂ (a b : F) : Algebra (first F a) (second F a b) :=
  (IntermediateField.inclusion (first_le_second F a b)).toRingHom.toAlgebra

instance algebra₂₃ (a b c : F) : Algebra (second F a b) (third F a b c) :=
  (IntermediateField.inclusion (second_le_third F a b c)).toRingHom.toAlgebra

instance algebra₁₃ (a b c : F) : Algebra (first F a) (third F a b c) :=
  (IntermediateField.inclusion (first_le_third F a b c)).toRingHom.toAlgebra

instance scalarTower₀₁₂ (a b : F) : IsScalarTower F (first F a) (second F a b) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance scalarTower₀₂₃ (a b c : F) : IsScalarTower F (second F a b) (third F a b c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance scalarTower₀₁₃ (a b c : F) : IsScalarTower F (first F a) (third F a b c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance scalarTower₁₂₃ (a b c : F) :
    IsScalarTower (first F a) (second F a b) (third F a b c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance finiteDimensional_first (a : F) : FiniteDimensional F (first F a) :=
  IntermediateField.adjoin.finiteDimensional (radical_integral F a)

instance finiteDimensional_second (a b : F) : FiniteDimensional F (second F a b) :=
  IntermediateField.finiteDimensional_adjoin_pair (radical_integral F a) (radical_integral F b)

instance finiteDimensional₁₂ (a b : F) : FiniteDimensional (first F a) (second F a b) :=
  Module.Finite.of_restrictScalars_finite F _ _

instance finiteDimensional₂₃ (a b c : F) : FiniteDimensional (second F a b) (third F a b c) :=
  Module.Finite.of_restrictScalars_finite F _ _

instance finiteDimensional₁₃ (a b c : F) : FiniteDimensional (first F a) (third F a b c) :=
  Module.Finite.of_restrictScalars_finite F _ _

instance separable_first [CharZero F] (a : F) : Algebra.IsSeparable F (first F a) :=
  inferInstance

instance separable₁₂ [CharZero F] (a b : F) :
    Algebra.IsSeparable (first F a) (second F a b) := inferInstance

instance separable₂₃ [CharZero F] (a b c : F) :
    Algebra.IsSeparable (second F a b) (third F a b c) := inferInstance

/-- The new root at the first stage. -/
def stepRoot₁ (a : F) : first F a :=
  ⟨radical F a, IntermediateField.subset_adjoin F _ (by simp)⟩

/-- The new root at the second stage. -/
def stepRoot₂ (a b : F) : second F a b :=
  ⟨radical F b, IntermediateField.subset_adjoin F _ (by simp)⟩

/-- The new root at the third stage. -/
def stepRoot₃ (a b c : F) : third F a b c := root₃ F a b c

@[simp] theorem stepRoot₁_sq (a : F) :
    stepRoot₁ F a ^ 2 = algebraMap F (first F a) a := by
  apply Subtype.ext
  exact radical_sq F a

@[simp] theorem stepRoot₂_sq (a b : F) :
    stepRoot₂ F a b ^ 2 = algebraMap (first F a) (second F a b)
      (algebraMap F (first F a) b) := by
  apply Subtype.ext
  exact radical_sq F b

@[simp] theorem stepRoot₃_sq (a b c : F) :
    stepRoot₃ F a b c ^ 2 = algebraMap (second F a b) (third F a b c)
      (algebraMap F (second F a b) c) := by
  apply Subtype.ext
  exact radical_sq F c

/-- The second field is exactly the first field with the second root adjoined. -/
theorem second_eq_relative_adjoin (a b : F) :
    second F a b = (IntermediateField.adjoin (first F a) {radical F b}).restrictScalars F := by
  have h := IntermediateField.adjoin_adjoin_left (F := F) (S := {radical F a})
    ({radical F b} : Set (AlgebraicClosure F))
  rw [Set.singleton_union] at h
  exact h.symm

/-- The third field is exactly the second field with the third root adjoined. -/
theorem third_eq_relative_adjoin (a b c : F) :
    third F a b c =
      (IntermediateField.adjoin (second F a b) {radical F c}).restrictScalars F := by
  have h := IntermediateField.adjoin_adjoin_left (F := F)
    (S := {radical F a, radical F b}) ({radical F c} : Set (AlgebraicClosure F))
  have hs : ({radical F a, radical F b} : Set (AlgebraicClosure F)) ∪ {radical F c} =
      {radical F a, radical F b, radical F c} := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hs] at h
  exact h.symm

/-- The first root generates the first field as an algebra. -/
theorem stepRoot₁_generates (a : F) : Algebra.adjoin F {stepRoot₁ F a} = ⊤ := by
  have hgen : IntermediateField.adjoin F {stepRoot₁ F a} = ⊤ := by
    apply IntermediateField.lift_injective (first F a)
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic _).mp hgen
  have h : IsAlgebraic F (stepRoot₁ F a) := (IsIntegral.of_finite F _).isAlgebraic
  simpa using h

/-- The second root generates the second field over the first as an algebra. -/
theorem stepRoot₂_generates (a b : F) :
    Algebra.adjoin (first F a) {stepRoot₂ F a b} = ⊤ := by
  exact Auxiliary.generator_top (first F a) (second F a b) (first_le_second F a b)
    (radical F b) (IntermediateField.subset_adjoin F _ (by simp))
    (second_eq_relative_adjoin F a b) (radical_integral F b).tower_top.isAlgebraic

/-- The third root generates the third field over the second as an algebra. -/
theorem stepRoot₃_generates (a b c : F) :
    Algebra.adjoin (second F a b) {stepRoot₃ F a b c} = ⊤ := by
  exact Auxiliary.generator_top (second F a b) (third F a b c) (second_le_third F a b c)
    (radical F c) (IntermediateField.subset_adjoin F _ (by simp))
    (third_eq_relative_adjoin F a b c) (radical_integral F c).tower_top.isAlgebraic

/-- The first step has degree two when its radicand is a nonsquare. -/
theorem finrank_first (a : F) (ha : ¬ IsSquare a) : Module.finrank F (first F a) = 2 := by
  apply finrank_adjoin_square_root F (radical_sq F a)
  intro u hu
  exact ha ⟨u, by simpa only [sq] using hu.symm⟩

/-- The first two independent square roots give absolute degree four. -/
theorem finrank_second (a b : F) (h2 : (2 : F) ≠ 0)
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) (hab : ¬ IsSquare (a * b)) :
    Module.finrank F (second F a b) = 4 := by
  have hd₁ := finrank_first F a ha
  have hd₂ : Module.finrank (first F a)
      (IntermediateField.adjoin (first F a) {radical F b}) = 2 := by
    apply finrank_adjoin_square_root (first F a) (a := algebraMap F _ b)
    · exact (radical_sq F b).trans (IsScalarTower.algebraMap_apply F (first F a)
        (AlgebraicClosure F) b)
    · intro u hu
      have hs : IsSquare (algebraMap F (first F a) b) :=
        ⟨u, by simpa only [sq] using hu.symm⟩
      rcases QuadraticSquareCriterion.square_criterion a b (radical F a)
          (radical_sq F a) ha h2 hs with h | h
      · exact hb h
      · exact hab h
  have hd := finrank_adjoin_union F ({radical F a} : Set (AlgebraicClosure F)) {radical F b}
  change Module.finrank F (IntermediateField.adjoin F ({radical F a} ∪ {radical F b})) =
    Module.finrank F (first F a) *
      Module.finrank (first F a) (IntermediateField.adjoin (first F a) {radical F b}) at hd
  rw [hd₁, hd₂] at hd
  rw [Set.singleton_union] at hd
  exact hd

/-- The second step has actual relative degree two. -/
theorem finrank₁₂ (a b c : F) (h2 : (2 : F) ≠ 0)
    (hind : IndependentSquareclasses F a b c) :
    Module.finrank (first F a) (second F a b) = 2 := by
  have h := Module.finrank_mul_finrank F (first F a) (second F a b)
  rw [finrank_first F a hind.first,
    finrank_second F a b h2 hind.first hind.second hind.first_second] at h
  omega

/-- The third step has actual relative degree two. -/
theorem finrank₂₃ (a b c : F) (h2 : (2 : F) ≠ 0)
    (hind : IndependentSquareclasses F a b c) :
    Module.finrank (second F a b) (third F a b c) = 2 := by
  have h := Module.finrank_mul_finrank F (second F a b) (third F a b c)
  rw [finrank_second F a b h2 hind.first hind.second hind.first_second,
    finrank_field_eq_eight F a b c h2 hind] at h
  omega

end FourCorner.Multiquadratic.Tower

#print axioms FourCorner.Multiquadratic.Tower.finrank₁₂
#print axioms FourCorner.Multiquadratic.Tower.finrank₂₃

#print axioms FourCorner.Multiquadratic.Tower.stepRoot₁_generates
#print axioms FourCorner.Multiquadratic.Tower.stepRoot₂_generates
#print axioms FourCorner.Multiquadratic.Tower.stepRoot₃_generates

#print axioms FourCorner.Multiquadratic.Tower.stepRoot₁_sq
#print axioms FourCorner.Multiquadratic.Tower.stepRoot₂_sq
#print axioms FourCorner.Multiquadratic.Tower.stepRoot₃_sq
#print axioms FourCorner.Multiquadratic.Tower.separable₁₂
#print axioms FourCorner.Multiquadratic.Tower.separable₂₃
