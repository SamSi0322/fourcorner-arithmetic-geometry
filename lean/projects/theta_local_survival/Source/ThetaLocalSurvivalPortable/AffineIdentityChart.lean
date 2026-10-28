import ThetaLocalSurvivalPortable.InfinitesimalGroupLinearization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication

/-- Every actual group scheme over QQ has an actual affine identity
chart and actual augmentation; no chart is assumed as extra data. -/
theorem exists_identity_chart (G : Over base) [GrpObj G] :
    ∃ (A : CommRingCat) (qmap : ℚ →+* A),
      letI : Algebra ℚ A := qmap.toAlgebra
      ∃ (j : pointObject A ⟶ G) (ε : A →ₐ[ℚ] ℚ),
        IsOpenImmersion j.left ∧ pointChange ε ≫ j=1 := by
  let e : pointObject ℚ ⟶ G := 1
  let x : G.left := e.left (IsLocalRing.closedPoint ℚ)
  obtain ⟨A,f,hf,hx,_⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X:=G.left) (U:=⊤) (show x∈(⊤ : G.left.Opens) from trivial)
  let qmap : ℚ →+* A := (Spec.preimage (f ≫ G.hom)).hom
  letI : Algebra ℚ A := qmap.toAlgebra
  letI : IsOpenImmersion f := hf
  have hb : f ≫ G.hom=(pointObject A).hom := (Spec.map_preimage (f ≫ G.hom)).symm
  let j : pointObject A ⟶ G := Over.homMk f hb
  have hr : Set.range e.left⊆Set.range f := by
    rintro _ ⟨y,rfl⟩
    rw [show y=IsLocalRing.closedPoint ℚ from Subsingleton.elim (α:=PrimeSpectrum ℚ) _ _]
    exact hx
  let l := IsOpenImmersion.lift f e.left hr
  have hl : l ≫ f=e.left := IsOpenImmersion.lift_fac _ _ _
  let q : pointObject ℚ ⟶ pointObject A := Over.homMk l (by
    rw [←hb,←Category.assoc,hl]
    exact e.w)
  let ε := pointToAlgHom A ℚ q
  refine ⟨A,qmap,j,ε,hf,?_⟩
  change pointChange (pointToAlgHom A ℚ q) ≫ j=e
  rw [pointChange_pointToAlgHom]
  apply Over.OverMorphism.ext
  exact hl

/-- Unique m-division in the actual square-zero identity kernel, now for
an arbitrary actual group scheme rather than a supplied chart. -/
theorem actual_infinitesimal_unique_root (G : Over base) [GrpObj G]
    (M : Type) [AddCommGroup M] [Module ℚ M] (m : ℕ) (hm : 0<m) (P : tangentPoints G M) :
    ∃! Q : tangentPoints G M,Q^m=P := by
  obtain ⟨A,qmap,h⟩ := exists_identity_chart G
  letI : Algebra ℚ A := qmap.toAlgebra
  obtain ⟨j,ε,hj,he⟩ := h
  letI := hj
  exact tangentPoints_unique_root G A j ε he m hm P

end FourCorner.ThetaLocalSurvival.Infinitesimal
