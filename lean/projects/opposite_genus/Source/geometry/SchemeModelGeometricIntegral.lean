import geometry.SchemeModelTwoAffineCover
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
Geometric integrality of the constructed proper model from the actual function
field after every extension of constants. Affine chart sections inject into the
function field; flat tensoring preserves these injections. The two actual chart
pullbacks therefore glue to an integral scheme.
-/

noncomputable section

namespace FourCorner.SchemeModelGeometricIntegral

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- Germs in the generic-point stalk respect the structural constant-field map. -/
theorem germ_constants (M : CurveModel K E) (U : M.C.Opens) [Nonempty U] (a : K) :
    (M.C.germToFunctionField U).hom
        ((Scheme.TwoAffineOpenCover.algebraOfHom M.toBase U).algebraMap a) =
      baseToFunctionField M.toBase a := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change (M.toBase.appLE ⊤ U le_top ≫ M.C.germToFunctionField U).hom _ =
    (M.toBase.appTop ≫ M.C.presheaf.germ ⊤ (genericPoint M.C) trivial).hom _
  congr 2
  rw [Scheme.Hom.appLE, Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  rfl

/-- The actual affine section ring embeds into the supplied function field of the model. -/
def sectionToField (M : CurveModel K E) (U : M.C.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase U
    Γ(M.C, U) →ₐ[K] E := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase U
  refine
    { M.ffEquiv.symm.toRingHom.comp (M.C.germToFunctionField U).hom with
      commutes' := ?_ }
  intro a
  change M.ffEquiv.symm ((M.C.germToFunctionField U).hom
    ((Scheme.TwoAffineOpenCover.algebraOfHom M.toBase U).algebraMap a)) = _
  rw [germ_constants]
  apply M.ffEquiv.injective
  rw [M.ffEquiv.apply_symm_apply]
  exact (M.ffEquiv_algebraMap a).symm

theorem sectionToField_injective (M : CurveModel K E) (U : M.C.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase U
    Function.Injective (sectionToField M U) :=
  M.ffEquiv.symm.injective.comp (M.C.germToFunctionField_injective U)

/-- Tensoring an actual chart with a constant field remains a domain whenever the
function-field tensor is a domain. -/
theorem isDomain_tensor_sections (M : CurveModel K E) (L : Type u) [Field L] [Algebra K L]
    [IsDomain (L ⊗[K] E)] (U : M.C.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase U
    IsDomain (L ⊗[K] Γ(M.C, U)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom M.toBase U
  let f : Γ(M.C, U) →ₐ[K] E := sectionToField M U
  let g : L ⊗[K] Γ(M.C, U) →ₐ[K] L ⊗[K] E :=
    Algebra.TensorProduct.map (AlgHom.id K L) f
  have hg : Function.Injective g := by
    change Function.Injective (f.toLinearMap.lTensor L)
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap
      (sectionToField_injective M U)
  exact Function.Injective.isDomain g.toRingHom hg

/-- Each actual constant-field pullback is integral, as derived from its two chart rings. -/
theorem isIntegral_pullback (M : CurveModel K E) (V : M.C.TwoAffineOpenCover)
    [Nonempty V.U0] [Nonempty V.U1] [Nonempty (V.U0 ⊓ V.U1 : M.C.Opens)]
    (L : Type u) [Field L] [Algebra K L] [IsDomain (L ⊗[K] E)] :
    IsIntegral (pullback M.toBase (Scheme.TwoAffineOpenCover.specMap K L)) := by
  have : IsDomain (L ⊗[K] (V.cover M.toBase).A0) := isDomain_tensor_sections M L V.U0
  have : IsDomain (L ⊗[K] (V.cover M.toBase).A1) := isDomain_tensor_sections M L V.U1
  have : IsDomain (L ⊗[K] (V.cover M.toBase).A01) :=
    isDomain_tensor_sections M L (V.U0 ⊓ V.U1)
  exact (V.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct M.toBase L).1

/-- Universal domain preservation for the actual function field implies geometric integrality. -/
theorem geometricallyIntegral (M : CurveModel K E) (V : M.C.TwoAffineOpenCover)
    [Nonempty V.U0] [Nonempty V.U1] [Nonempty (V.U0 ⊓ V.U1 : M.C.Opens)]
    (hgeom : ∀ (L : Type u) [Field L] [Algebra K L], IsDomain (L ⊗[K] E)) :
    GeometricallyIntegral M.toBase := by
  refine ⟨geometrically_iff_of_commRing.mpr ?_⟩
  intro L _ _ Y fst snd hpb
  have := hgeom L
  have : IsIntegral (pullback M.toBase (Scheme.TwoAffineOpenCover.specMap K L)) :=
    isIntegral_pullback M V L
  have : Nonempty Y := Nonempty.map hpb.isoPullback.inv.base inferInstance
  exact isIntegral_of_isOpenImmersion hpb.isoPullback.hom

variable (K E) [CharZero K] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E]

/-- The concrete constructed model is geometrically integral; no model or cover is assumed. -/
theorem model_geometricallyIntegral
    (hgeom : ∀ (L : Type u) [Field L] [Algebra K L], IsDomain (L ⊗[K] E)) :
    GeometricallyIntegral (SchemeModelFiniteExtension.model K E).toBase :=
  geometricallyIntegral (SchemeModelFiniteExtension.model K E)
    (SchemeModelFiniteExtension.twoAffineOpenCover K E) hgeom

end FourCorner.SchemeModelGeometricIntegral

#check @FourCorner.SchemeModelGeometricIntegral.model_geometricallyIntegral
#print axioms FourCorner.SchemeModelGeometricIntegral.sectionToField
#print axioms FourCorner.SchemeModelGeometricIntegral.isDomain_tensor_sections
#print axioms FourCorner.SchemeModelGeometricIntegral.isIntegral_pullback
#print axioms FourCorner.SchemeModelGeometricIntegral.geometricallyIntegral
#print axioms FourCorner.SchemeModelGeometricIntegral.model_geometricallyIntegral
