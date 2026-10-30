import ThetaCoverClassPortable.ActualGeometricCoverClass
import ThetaCoverClassPortable.ActualDictionaryClassCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard
open scoped CategoryTheory.MonObj
namespace FourCorner.ActualGeometricCoverDeltaComparison
open ThetaDGeometricModel
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth

/-- The SAME represented point with the actual geometric Kummer line is
exactly the native boundary-minus-infinity delta under the genuine Poincare
Pic0 dictionary, with the model's native generic-stalk compatibility retained. -/
theorem exists_actual_geometric_delta_dictionary
    [GeometricallyIntegral toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) toBase)
    (𝔉 : SmoothProperCurve.FiniteMapData toBase ε)
    (J : RelativePic0Designation K toBase)
    (h : RepresentsRelSubPic toBase ε (algEquivZeroCut toBase ε) J)
    (p : Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk J.toBase)
    (hL : Nonempty ((Scheme.Modules.pullback (toProdSpec toBase)).obj
      (h.poincare.pullbackAlong ⟨p.left,Over.w p⟩).L ≅ ThetaGeometricKummerLine.L)) :
    letI := (show RepresentsRelSubPic toBase ε (algEquivZeroGroupCut toBase ε).toSubPicCondition J from h).grpObj
    ∃ (M : CurveModel K field) (i : geometricD ≅ M.C),
      i.hom ≫ M.toBase=toBase ∧
      geometricD.fromSpecStalk (genericPoint geometricD) ≫ i.hom=
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ M.C.fromSpecStalk (genericPoint M.C) ∧
      ∃ pts : Pic0 K field ≃ (Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk J.toBase),
        (∀ a b,pts (a+b)=pts a*pts b) ∧ pts ThetaCoverPic0.delta=p := by
  classical
  letI := (show RepresentsRelSubPic toBase ε (algEquivZeroGroupCut toBase ε).toSubPicCondition J from h).grpObj
  obtain ⟨M,i,hi,hgeneric⟩ := NativeCurveModelExistence.exists_model toBase
  let ε' : {q : Spec (.of K) ⟶ M.C // q ≫ M.toBase=𝟙 _} :=
    ⟨ε.val ≫ i.hom,by rw [Category.assoc,hi];exact ε.property⟩
  have he : i.inv ≫ toBase=M.toBase :=
    (congrArg (i.inv ≫ ·) hi.symm).trans (i.inv_hom_id_assoc M.toBase)
  have hε : ε'.val ≫ i.inv=ε.val := by
    simp only [ε',Category.assoc,Iso.hom_inv_id,Category.comp_id]
  obtain ⟨cl,hcl_iso,hcl_tensor,hcl_one,hcl_pt,-⟩ := AlgebraicCurve.CurveModel.exists_divisorClassMap M
  obtain ⟨pts,hmul,hclass⟩ := exists_dictionary_with_class K toBase ε 𝔉 J h M i.symm he ε' hε
    cl hcl_iso hcl_tensor hcl_one hcl_pt
  refine ⟨M,i,hi,hgeneric,pts,hmul,?_⟩
  apply (dictionary_point_eq_iff_class K toBase ε J h M i.symm cl pts hclass p ThetaCoverPic0.zeroDegreeDivisor).mpr
  obtain ⟨eL⟩ := hL
  have hiL : (Scheme.Modules.pullback (i.inv ≫ toProdSpec toBase)).obj
      (h.poincare.pullbackAlong ⟨p.left,Over.w p⟩).L ≅
      (Scheme.Modules.pullback i.inv).obj ThetaGeometricKummerLine.L :=
    ((Scheme.Modules.pullbackComp i.inv (toProdSpec toBase)).app _).symm ≪≫
      (Scheme.Modules.pullback i.inv).mapIso eL
  exact (hcl_iso _ _ ((h.poincare.pullbackAlong _).isInvertible.pullback _) ⟨hiL⟩).trans
    (actual_geometric_cover_class M i hi hgeneric cl hcl_iso hcl_tensor hcl_one hcl_pt)

end FourCorner.ActualGeometricCoverDeltaComparison
