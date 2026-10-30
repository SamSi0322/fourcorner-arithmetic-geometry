import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! Genuine affine coordinate rings of manuscript (ell-original) and (ell-diagonal).
No integrality or identification of X_n is asserted in this module. -/
noncomputable section
namespace FourCorner.OriginalCoverCompletion
open MvPolynomial

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def originalRelations (z : Fin 6 → A) : Fin 4 → A :=
 ![z 2 ^ 2 - z 0 ^ 2 - z 1 ^ 2,
   z 3 ^ 2 - (z 0 - 1)^2 - z 1 ^ 2,
   z 4 ^ 2 - z 0 ^ 2 - (z 1 - 1)^2,
   z 5 ^ 2 - (z 0 - 1)^2 - (z 1 - 1)^2]

def diagonalRelations (z : Fin 4 → A) : Fin 2 → A :=
 ![z 0 ^ 2 + z 1 ^ 2 - z 2 ^ 2 - z 3 ^ 2,
   (z 0 ^ 2 - 2)*(2-z 1 ^ 2) - z 2 ^ 2*z 3 ^ 2]

/-- Exactly the manuscript's x,y,r0,r1,r2,r3, with every radius retained. -/
def returnOriginal (z : Fin 4 → A) : Fin 6 → A :=
 ![(1/2 : ℚ) • 1 + (1/4 : ℚ) • (z 0*z 1+z 2*z 3),
   (1/2 : ℚ) • 1 + (1/4 : ℚ) • (z 0*z 1-z 2*z 3),
   (1/2 : ℚ) • (z 0+z 1), (1/2 : ℚ) • (z 2-z 3),
   (1/2 : ℚ) • (z 2+z 3), (1/2 : ℚ) • (z 0-z 1)]

def toDiagonal (z : Fin 6 → A) : Fin 4 → A :=
 ![z 2+z 5, z 2-z 5, z 3+z 4, z 4-z 3]

theorem return_relations (z : Fin 4 → A)
    (h : ∀ i, diagonalRelations z i = 0) :
    ∀ i, originalRelations (returnOriginal z) i = 0 := by
  have h0 := h 0; have h1 := h 1
  simp [diagonalRelations] at h0 h1
  intro i; fin_cases i <;> simp [originalRelations, returnOriginal]
  · linear_combination (norm := algebra) (1/8 : ℚ) • h1
  · linear_combination (norm := algebra) (1/8 : ℚ) • h1 - (1/4 : ℚ) • h0
  · linear_combination (norm := algebra) (1/8 : ℚ) • h1 - (1/4 : ℚ) • h0
  · linear_combination (norm := algebra) (1/8 : ℚ) • h1

theorem diagonal_relations (z : Fin 6 → A)
    (h : ∀ i, originalRelations z i = 0) :
    ∀ i, diagonalRelations (toDiagonal z) i = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [originalRelations] at h0 h1 h2 h3
  have hs : (z 2+z 5)*(z 2-z 5)-2*(z 0+z 1-1)=0 := by
    linear_combination h0-h3
  have ht : (z 3+z 4)*(z 4-z 3)-2*(z 0-z 1)=0 := by
    linear_combination h2-h1
  intro i; fin_cases i <;> simp [diagonalRelations, toDiagonal]
  · linear_combination 2*(h0+h3-h1-h2)
  · linear_combination 4*h0+4*h3 - ((z 2+z 5)*(z 2-z 5)+2*(z 0+z 1-1))*hs -
      ((z 3+z 4)*(z 4-z 3)+2*(z 0-z 1))*ht

theorem diagonal_return (z : Fin 4 → A) : toDiagonal (returnOriginal z) = z := by
  funext i; fin_cases i <;> simp [toDiagonal, returnOriginal] <;> algebra

theorem original_return (z : Fin 6 → A)
    (h : ∀ i, originalRelations z i = 0) : returnOriginal (toDiagonal z) = z := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [originalRelations] at h0 h1 h2 h3
  funext i; fin_cases i <;> simp [returnOriginal, toDiagonal]
  · linear_combination (norm := algebra) (1/4 : ℚ) • (h0-h3+h2-h1)
  · linear_combination (norm := algebra) (1/4 : ℚ) • (h0-h3-h2+h1)
  all_goals algebra

abbrev OriginalPoly := MvPolynomial (Fin 6) ℚ
abbrev DiagonalPoly := MvPolynomial (Fin 4) ℚ

def originalIdeal : Ideal OriginalPoly := Ideal.span (Set.range (originalRelations X))
def diagonalIdeal : Ideal DiagonalPoly := Ideal.span (Set.range (diagonalRelations X))

/-- The actual four-distance affine coordinate ring, not a field chosen by its conclusion. -/
abbrev OriginalRing := OriginalPoly ⧸ originalIdeal
/-- The actual two-equation diagonal affine coordinate ring. -/
abbrev DiagonalRing := DiagonalPoly ⧸ diagonalIdeal

def originalCoordinates : Fin 6 → OriginalRing := fun i => Ideal.Quotient.mk originalIdeal (X i)
def diagonalCoordinates : Fin 4 → DiagonalRing := fun i => Ideal.Quotient.mk diagonalIdeal (X i)

@[simp] theorem eval_original (z : Fin 6 → A) (i : Fin 4) :
    aeval z (originalRelations (X : Fin 6 → OriginalPoly) i) = originalRelations z i := by
  fin_cases i <;> simp [originalRelations]
@[simp] theorem eval_diagonal (z : Fin 4 → A) (i : Fin 2) :
    aeval z (diagonalRelations (X : Fin 4 → DiagonalPoly) i) = diagonalRelations z i := by
  fin_cases i <;> simp [diagonalRelations]

 theorem original_coordinates_relations : ∀ i, originalRelations originalCoordinates i = 0 := by
  intro i
  have hm : originalRelations (X : Fin 6 → OriginalPoly) i ∈ originalIdeal :=
    Ideal.subset_span (Set.mem_range_self i)
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  fin_cases i <;> simpa [originalRelations, originalCoordinates, map_sub, map_add, map_pow] using hz
 theorem diagonal_coordinates_relations : ∀ i, diagonalRelations diagonalCoordinates i = 0 := by
  intro i
  have hm : diagonalRelations (X : Fin 4 → DiagonalPoly) i ∈ diagonalIdeal :=
    Ideal.subset_span (Set.mem_range_self i)
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  fin_cases i <;> simpa [diagonalRelations, diagonalCoordinates, map_sub, map_add, map_mul, map_pow, map_ofNat] using hz

def originalLift (z : Fin 6 → A) (h : ∀ i, originalRelations z i = 0) : OriginalRing →ₐ[ℚ] A :=
  Ideal.Quotient.liftₐ originalIdeal (aeval z) (by
    have hker : originalIdeal ≤ RingHom.ker (aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (eval_original z i).trans (h i)
    intro p hp; exact hker hp)

def diagonalLift (z : Fin 4 → A) (h : ∀ i, diagonalRelations z i = 0) : DiagonalRing →ₐ[ℚ] A :=
  Ideal.Quotient.liftₐ diagonalIdeal (aeval z) (by
    have hker : diagonalIdeal ≤ RingHom.ker (aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (eval_diagonal z i).trans (h i)
    intro p hp; exact hker hp)

@[simp] theorem originalLift_coordinate (z : Fin 6 → A) (h) (i) :
    originalLift z h (originalCoordinates i) = z i := by
  change aeval z (X i) = z i
  simp
@[simp] theorem diagonalLift_coordinate (z : Fin 4 → A) (h) (i) :
    diagonalLift z h (diagonalCoordinates i) = z i := by
  change aeval z (X i) = z i
  simp

def originalToDiagonal : OriginalRing →ₐ[ℚ] DiagonalRing :=
  originalLift (returnOriginal diagonalCoordinates) (return_relations _ diagonal_coordinates_relations)
def diagonalToOriginal : DiagonalRing →ₐ[ℚ] OriginalRing :=
  diagonalLift (toDiagonal originalCoordinates) (diagonal_relations _ original_coordinates_relations)

 theorem original_ext {f g : OriginalRing →ₐ[ℚ] A}
    (h : ∀ i, f (originalCoordinates i) = g (originalCoordinates i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h
 theorem diagonal_ext {f g : DiagonalRing →ₐ[ℚ] A}
    (h : ∀ i, f (diagonalCoordinates i) = g (diagonalCoordinates i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

 theorem original_comp : diagonalToOriginal.comp originalToDiagonal = AlgHom.id ℚ OriginalRing := by
  apply original_ext
  intro i
  change diagonalToOriginal (originalToDiagonal (originalCoordinates i)) = originalCoordinates i
  rw [originalToDiagonal, originalLift_coordinate]
  have hi := congrFun (original_return originalCoordinates original_coordinates_relations) i
  fin_cases i <;> simp [returnOriginal, toDiagonal, diagonalToOriginal, map_add, map_sub, map_mul] at hi ⊢ <;> linear_combination (norm := algebra) hi
 theorem diagonal_comp : originalToDiagonal.comp diagonalToOriginal = AlgHom.id ℚ DiagonalRing := by
  apply diagonal_ext
  intro i
  change originalToDiagonal (diagonalToOriginal (diagonalCoordinates i)) = diagonalCoordinates i
  rw [diagonalToOriginal, diagonalLift_coordinate]
  have hi := congrFun (diagonal_return diagonalCoordinates) i
  fin_cases i <;> simpa [returnOriginal, toDiagonal, originalToDiagonal, map_add, map_sub] using hi

/-- A true isomorphism of the two independently presented affine coordinate rings. -/
def originalDiagonalEquiv : OriginalRing ≃ₐ[ℚ] DiagonalRing :=
  AlgEquiv.ofAlgHom originalToDiagonal diagonalToOriginal diagonal_comp original_comp

#print axioms originalDiagonalEquiv
#print axioms original_comp
#print axioms diagonal_comp
#print axioms original_return
#print axioms return_relations
#print axioms diagonal_relations
end FourCorner.OriginalCoverCompletion
