import OriginalDiagonalPresentation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Real.Sqrt

/-! Actual original-surface sign automorphism and degree-obstruction identity.
The function-field section states, rather than conceals, its two remaining inputs:
originalRing is a domain and minus one is not a square in its fraction field. -/
noncomputable section
namespace FourCorner.OriginalCoverCompletion

def flipRadius0 {A : Type*} [CommRing A] (z : Fin 6 → A) : Fin 6 → A :=
 ![z 0,z 1,-z 2,z 3,z 4,z 5]

theorem flip_relations {A : Type*} [CommRing A] [Algebra ℚ A]
    (z : Fin 6 → A) (h : ∀ i, originalRelations z i = 0) :
    ∀ i, originalRelations (flipRadius0 z) i = 0 := by
  intro i; have hi := h i
  fin_cases i <;> simpa [originalRelations, flipRadius0] using hi

def deck0Hom : OriginalRing →ₐ[ℚ] OriginalRing :=
 originalLift (flipRadius0 originalCoordinates) (flip_relations _ original_coordinates_relations)

@[simp] theorem deck0Hom_coordinate (i : Fin 6) :
    deck0Hom (originalCoordinates i) = flipRadius0 originalCoordinates i :=
  originalLift_coordinate _ _ _

theorem deck0_comp : deck0Hom.comp deck0Hom = AlgHom.id ℚ OriginalRing := by
  apply original_ext
  intro i
  change deck0Hom (deck0Hom (originalCoordinates i)) = originalCoordinates i
  rw [deck0Hom_coordinate]
  fin_cases i <;> simp [flipRadius0, map_neg]

/-- The actual sign change of r0 is an algebra automorphism of the original coordinate ring. -/
def deck0 : OriginalRing ≃ₐ[ℚ] OriginalRing :=
  AlgEquiv.ofAlgHom deck0Hom deck0Hom deck0_comp deck0_comp

@[simp] theorem deck0_coordinate (i : Fin 6) :
    deck0 (originalCoordinates i) = flipRadius0 originalCoordinates i :=
  deck0Hom_coordinate i

def tPlus {A : Type*} [CommRing A] (z : Fin 6 → A) := z 2*z 5+z 3*z 4
def tMinus {A : Type*} [CommRing A] (z : Fin 6 → A) := z 2*z 5-z 3*z 4

/-- The product obstruction uses the literal four-distance equations only. -/
theorem conjugate_product {A : Type*} [CommRing A] [Algebra ℚ A]
    (z : Fin 6 → A) (h : ∀ i, originalRelations z i = 0) :
    (tPlus z ^ 2-1)*(tMinus z ^ 2-1) = -4*(z 0-z 1)^2*(z 0+z 1-1)^2 := by
  have h0 : z 2^2 = z 0^2+z 1^2 := by
    have hh := h 0; simp [originalRelations] at hh; linear_combination hh
  have h1 : z 3^2 = (z 0-1)^2+z 1^2 := by
    have hh := h 1; simp [originalRelations] at hh; linear_combination hh
  have h2 : z 4^2 = z 0^2+(z 1-1)^2 := by
    have hh := h 2; simp [originalRelations] at hh; linear_combination hh
  have h3 : z 5^2 = (z 0-1)^2+(z 1-1)^2 := by
    have hh := h 3; simp [originalRelations] at hh; linear_combination hh
  calc
    _ = ((z 2)^2*(z 5)^2+(z 3)^2*(z 4)^2-1)^2-
        4*((z 2)^2*(z 5)^2)*((z 3)^2*(z 4)^2) := by simp only [tPlus,tMinus]; ring
    _ = _ := by rw [h0,h1,h2,h3]; ring

 theorem deck0_tPlus : deck0 (tPlus originalCoordinates) = -tMinus originalCoordinates := by
  simp [tPlus,tMinus,map_add,map_mul,flipRadius0]; ring
 theorem deck0_tMinus : deck0 (tMinus originalCoordinates) = -tPlus originalCoordinates := by
  simp [tPlus,tMinus,map_sub,map_mul,flipRadius0]; ring

/-- Corner evaluations verify the generic diagonal differences are nonzero in the
actual original ring, independently of a future domain proof. -/
def corner00 : OriginalRing →ₐ[ℚ] ℝ :=
  originalLift ![0,0,0,1,1,Real.sqrt 2] (by
    intro i; fin_cases i
    · change (0:ℝ)^2-0^2-0^2=0; norm_num
    · change (1:ℝ)^2-(0-1)^2-0^2=0; norm_num
    · change (1:ℝ)^2-0^2-(0-1)^2=0; norm_num
    · change (Real.sqrt 2)^2-(0-1)^2-(0-1)^2=0
      norm_num [Real.sq_sqrt])
def corner10 : OriginalRing →ₐ[ℚ] ℝ :=
  originalLift ![1,0,1,0,Real.sqrt 2,1] (by
    intro i; fin_cases i
    · change (1:ℝ)^2-1^2-0^2=0; norm_num
    · change (0:ℝ)^2-(1-1)^2-0^2=0; norm_num
    · change (Real.sqrt 2)^2-1^2-(0-1)^2=0
      norm_num [Real.sq_sqrt]
    · change (1:ℝ)^2-(1-1)^2-(0-1)^2=0; norm_num)

 theorem original_x_sub_y_ne_zero : originalCoordinates 0-originalCoordinates 1 ≠ 0 := by
  intro he
  have hh := congrArg corner10 he
  norm_num [map_sub,corner10] at hh
 theorem original_x_add_y_sub_one_ne_zero :
    originalCoordinates 0+originalCoordinates 1-1 ≠ 0 := by
  intro he
  have hh := congrArg corner00 he
  norm_num [map_sub,map_add,corner00] at hh

section FunctionField
variable [IsDomain OriginalRing]

/-- Actual fraction ring of the original four-equation coordinate ring.
Its use as a field in this section requires the displayed domain instance. -/
abbrev OriginalFunctionField := FractionRing OriginalRing

def fieldCoordinates : Fin 6 → OriginalFunctionField :=
  fun i => algebraMap OriginalRing OriginalFunctionField (originalCoordinates i)

def fieldDeck0 : OriginalFunctionField ≃ₐ[ℚ] OriginalFunctionField :=
  IsFractionRing.algEquivOfAlgEquiv deck0

@[simp] theorem fieldDeck0_coordinate (i : Fin 6) :
    fieldDeck0 (fieldCoordinates i) = flipRadius0 fieldCoordinates i := by
  rw [fieldCoordinates, fieldDeck0, IsFractionRing.algEquivOfAlgEquiv_algebraMap,deck0_coordinate]
  fin_cases i <;> simp [flipRadius0,fieldCoordinates,map_neg]

 theorem field_coordinates_relations : ∀ i, originalRelations fieldCoordinates i = 0 := by
  intro i
  have hi := congrArg (algebraMap OriginalRing OriginalFunctionField) (original_coordinates_relations i)
  fin_cases i <;> simpa [originalRelations,fieldCoordinates,map_sub,map_add,map_pow] using hi

 theorem field_x_sub_y_ne_zero : fieldCoordinates 0-fieldCoordinates 1 ≠ 0 := by
  simpa [fieldCoordinates,← map_sub] using
    (IsFractionRing.injective OriginalRing OriginalFunctionField).ne (by simpa using original_x_sub_y_ne_zero)
 theorem field_x_add_y_sub_one_ne_zero : fieldCoordinates 0+fieldCoordinates 1-1 ≠ 0 := by
  intro he
  apply original_x_add_y_sub_one_ne_zero
  apply IsFractionRing.injective OriginalRing OriginalFunctionField
  simpa [map_sub,map_add,fieldCoordinates] using he

 theorem fieldDeck0_tPlus : fieldDeck0 (tPlus fieldCoordinates) = -tMinus fieldCoordinates := by
  simp [tPlus,tMinus,map_add,map_mul,flipRadius0]; ring

/-- A concrete sufficient final input for nonsquareness of the exact manuscript radicand.
It is not a completed assertion that the original ring is integral or formally real. -/
theorem original_radicand_nonsquare_of_minus_one (n : ℚ) (hn : n ≠ 0)
    (hreal : ¬ IsSquare (-1 : OriginalFunctionField)) :
    ¬ IsSquare ((tPlus fieldCoordinates ^ 2-1)/(algebraMap ℚ OriginalFunctionField n)) := by
  intro hs
  obtain ⟨v,hv⟩ := hs
  let N : OriginalFunctionField := algebraMap ℚ OriginalFunctionField n
  have hN : N ≠ 0 := (map_ne_zero (algebraMap ℚ OriginalFunctionField)).mpr hn
  have hv2 : v^2 = (tPlus fieldCoordinates^2-1)/N := by simpa [N,sq] using hv.symm
  have hvN : v^2*N = tPlus fieldCoordinates^2-1 := (eq_div_iff hN).mp hv2
  have hwN : (fieldDeck0 v)^2*N = tMinus fieldCoordinates^2-1 := by
    have hh := congrArg fieldDeck0 hvN
    simpa [N,map_mul,map_pow,map_sub,fieldDeck0_tPlus] using hh
  let D := 2*(fieldCoordinates 0-fieldCoordinates 1)*(fieldCoordinates 0+fieldCoordinates 1-1)
  have hD : D ≠ 0 := mul_ne_zero (mul_ne_zero (by
      have hh : (2 : OriginalFunctionField) ≠ 0 := by
        intro hh
        apply hreal
        refine ⟨1, ?_⟩
        linear_combination -hh
      exact hh) field_x_sub_y_ne_zero)
    field_x_add_y_sub_one_ne_zero
  have hprod := conjugate_product fieldCoordinates field_coordinates_relations
  have he : (v*(fieldDeck0 v)*N)^2 = -(D^2) := by
    calc
      _ = (v^2*N)*((fieldDeck0 v)^2*N) := by ring
      _ = _ := by rw [hvN,hwN,hprod]; dsimp [D]; ring
  apply hreal
  refine ⟨v*(fieldDeck0 v)*N/D, ?_⟩
  rw [← sq,div_pow,he]
  field_simp

end FunctionField

#print axioms deck0
#print axioms conjugate_product
#print axioms original_x_sub_y_ne_zero
#print axioms original_x_add_y_sub_one_ne_zero
#print axioms fieldDeck0
#print axioms original_radicand_nonsquare_of_minus_one
end FourCorner.OriginalCoverCompletion
