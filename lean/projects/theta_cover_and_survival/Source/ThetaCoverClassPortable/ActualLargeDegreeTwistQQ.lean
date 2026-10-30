import ThetaCoverClassPortable.ActualLargeDegreeTwistFMD
import ThetaCoverClassPortable.NativeCurveModelExistence
import Mathlib.Algebra.CharP.Algebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra
universe u
namespace FourCorner.ActualPicardProperties

/-- For an actual characteristic-zero field curve, construct its true model
and RR internally, then apply the actual-FMD large-degree cohomology theorem. -/
theorem largeDegreeTwist_of_RR_genus_QQ
    {k : Type u} [Field k] [IsAlgClosed k] [Algebra ℚ k]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of k)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (g : ℕ)
    (hg : ∀ (F : Type u) [Field F] [Algebra k F] (M : CurveModel k F) (e : M.C ≅ C)
      (_ : e.hom ≫ c=M.toBase) (Kc : Divisor k F) (g' : ℕ),
      (∀ D : Divisor k F, (ell D : ℤ)-ell (Kc-D)=Divisor.degree D+1-g') → g'=g)
    (L : C.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero c L)
    (r : ℕ) (hr : 2*g ≤ r+1) (V : C.TwoAffineOpenCover) :
    Subsingleton (V.sectionsOf c (L ⊗ ((ε.1.ker)^r).invModule)).H1 ∧
      Module.finrank k (V.sectionsOf c (L ⊗ ((ε.1.ker)^r).invModule)).H0=r+1-g := by
  letI : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  letI := (baseToFunctionField c).toAlgebra
  haveI : IsCurveOver k C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType k C.functionField := essFiniteType_functionField c
  obtain ⟨M,i,hi,_⟩ := NativeCurveModelExistence.exists_model c
  let e : M.C ≅ C := i.symm
  have he : e.hom ≫ c = M.toBase := by
    change i.inv ≫ c = M.toBase
    have z := congrArg (i.inv ≫ ·) hi
    simpa only [←Category.assoc,Iso.inv_hom_id,Category.id_comp] using z.symm
  have hei : e.inv ≫ M.toBase = c := by rw [←he,Iso.inv_hom_id_assoc]
  let εM : {p : Spec (.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
    ⟨ε.1 ≫ e.inv,by rw [Category.assoc,hei];exact ε.2⟩
  have hε : εM.1 ≫ e.hom=ε.1 := by
    change (ε.1 ≫ e.inv) ≫ e.hom = ε.1
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  obtain ⟨Kc,hRR⟩ := RiemannRochWithGenusFF.exists_rr (K:=k) (F:=C.functionField)
  have hgen := hg C.functionField M e he Kc _ hRR
  have hRRg : ∀ D : Divisor k C.functionField,
      (ell D : ℤ)-ell (Kc-D)=Divisor.degree D+1-g := by simpa only [hgen] using hRR
  exact largeDegreeTwist_of_model_RR c ε 𝔉 M e he εM hε Kc g hRRg L hL h0 r hr V

#print axioms largeDegreeTwist_of_RR_genus_QQ
end FourCorner.ActualPicardProperties
