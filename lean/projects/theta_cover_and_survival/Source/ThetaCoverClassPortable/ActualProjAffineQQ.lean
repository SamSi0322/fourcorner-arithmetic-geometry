import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FourCorner.ActualPicardProperties

/-- A finite set of points of standard projective space over a QQ-algebra
is contained in the basic open of an actual homogeneous linear form. -/
theorem exists_linearForm_basicOpen_contains
    (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ)
    (S : Finset (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))) :
    ∃ f : MvPolynomial (Fin (n + 1)) R,
      f ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 ∧
      ∀ x ∈ S, x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) f := by
  classical
  let H := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1
  let p (x : S) : Submodule ℚ H :=
    { carrier := {f | f.val ∈ x.val.asHomogeneousIdeal.toIdeal}
      zero_mem' := (x.val.asHomogeneousIdeal.toIdeal).zero_mem
      add_mem' := fun hf hg => (x.val.asHomogeneousIdeal.toIdeal).add_mem hf hg
      smul_mem' := fun a f hf => by
        change a • (f.val) ∈ x.val.asHomogeneousIdeal.toIdeal
        rw [Algebra.smul_def]
        exact (x.val.asHomogeneousIdeal.toIdeal).mul_mem_left _ hf }
  have hp (x : S) : p x ≠ ⊤ := by
    intro htop
    apply x.val.not_irrelevant_le
    apply (ProjSpace.irrelevant_le_span_X R n).trans
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hx : (⟨MvPolynomial.X i, ProjSpace.X_mem_one R n i⟩ : H) ∈ p x := by
      rw [htop]; trivial
    exact hx
  obtain ⟨f,hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨f.val,f.property,fun x hx => hf ⟨x,hx⟩⟩

/-- Actual affine-neighbourhood property for a scheme mapping affinely to
standard projective space over a QQ-algebra. -/
theorem exists_isAffineOpen_forall_mem_of_isAffineHom_standardProj_QQ
    (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) {X : Scheme}
    (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom ι]
    (S : Finset X) : ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by
  classical
  obtain ⟨f,hf,hS⟩ := exists_linearForm_basicOpen_contains R n (S.image ι)
  refine ⟨ι ⁻¹ᵁ (Proj.basicOpen _ f), (Proj.isAffineOpen_basicOpen _ f hf (by omega)).preimage ι, ?_⟩
  intro x hx
  exact hS (ι x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

#print axioms exists_isAffineOpen_forall_mem_of_isAffineHom_standardProj_QQ
end FourCorner.ActualPicardProperties
