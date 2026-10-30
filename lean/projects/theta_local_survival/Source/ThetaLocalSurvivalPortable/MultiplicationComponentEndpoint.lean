import ThetaLocalSurvivalPortable.DescendedComponentScheme
import ThetaLocalSurvivalPortable.AbelianMultiplicationEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.MonObj
namespace FourCorner.ThetaLocalSurvival.ComponentDescent
open Multiplication
variable (G X : Over qqBase) [GrpObj G]

def multiplicationCoverBase (a : X ⟶ G) (m : ℕ) : cover G X a m ⟶ qqBase :=
  pullback.fst a.left (multiplication G m) ≫ X.hom
abbrev multiplicationCoverOrigin (a : X ⟶ G) (O : rationalBase ⟶ X) (hO : O ≫ a=1) (m : ℕ) :=
  originLift G X a O hO m

theorem multiplicationCoverOrigin_over (a : X ⟶ G) (O : rationalBase ⟶ X) (hO : O ≫ a=1) (m : ℕ) :
    multiplicationCoverOrigin G X a O hO m ≫ multiplicationCoverBase G X a m=𝟙 qqBase := by
  rw [multiplicationCoverBase,←Category.assoc,originLift_fst]
  exact O.w

variable [IsProper G.hom] [GeometricallyIntegral G.hom] [IsProper X.hom]

theorem multiplicationCoverBase_proper (a : X ⟶ G) (m : ℕ) (hm : 1≤m) :
    IsProper (multiplicationCoverBase G X a m) := by
  obtain ⟨hf,_⟩ := abelian_cover_finite_etale G X a m hm
  letI := hf
  unfold multiplicationCoverBase
  infer_instance

variable (a : X ⟶ G) (O : rationalBase ⟶ X) (hO : O ≫ a=1) (m : ℕ) (hm : 1≤m)

/-- The actual distinguished QQ component of the literal multiplication
pullback, constructed by the proved effective geometric descent. -/
def multiplicationComponent : Scheme := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact descendedComponent (multiplicationCoverBase G X a m) (multiplicationCoverOrigin G X a O hO m)
    (multiplicationCoverOrigin_over G X a O hO m)

def multiplicationComponentToBase : multiplicationComponent G X a O hO m hm ⟶ qqBase := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact descendedToBase (multiplicationCoverBase G X a m) (multiplicationCoverOrigin G X a O hO m)
    (multiplicationCoverOrigin_over G X a O hO m)

def multiplicationComponentOrigin : qqBase ⟶ multiplicationComponent G X a O hO m hm := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact descendedOrigin (multiplicationCoverBase G X a m) (multiplicationCoverOrigin G X a O hO m)
    (multiplicationCoverOrigin_over G X a O hO m)

def multiplicationComponentProjection : multiplicationComponent G X a O hO m hm ⟶ X.left := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact (descendedOpen (multiplicationCoverBase G X a m) (multiplicationCoverOrigin G X a O hO m)
    (multiplicationCoverOrigin_over G X a O hO m)).ι ≫ pullback.fst a.left (multiplication G m)

@[reassoc (attr := simp)] theorem multiplicationComponentOrigin_projection :
    multiplicationComponentOrigin G X a O hO m hm ≫ multiplicationComponentProjection G X a O hO m hm=O.left := by
  letI := multiplicationCoverBase_proper G X a m hm
  change descendedOrigin _ _ _ ≫ ((descendedOpen _ _ _).ι ≫ pullback.fst a.left (multiplication G m))=O.left
  rw [←Category.assoc,descendedOrigin_inclusion,originLift_fst]

theorem multiplicationComponentOrigin_over :
    multiplicationComponentOrigin G X a O hO m hm ≫ multiplicationComponentToBase G X a O hO m hm=𝟙 qqBase := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact descendedOrigin_over _ _ _

@[reassoc (attr := simp)] theorem multiplicationComponentProjection_over :
    multiplicationComponentProjection G X a O hO m hm ≫ X.hom=multiplicationComponentToBase G X a O hO m hm := by
  letI := multiplicationCoverBase_proper G X a m hm
  change ((descendedOpen _ _ _).ι ≫ pullback.fst a.left (multiplication G m)) ≫ X.hom=
    (descendedOpen _ _ _).ι ≫ (pullback.fst a.left (multiplication G m) ≫ X.hom)
  exact Category.assoc _ _ _

theorem multiplicationComponentProjection_finite_etale :
    IsFinite (multiplicationComponentProjection G X a O hO m hm) ∧
      Etale (multiplicationComponentProjection G X a O hO m hm) := by
  letI := multiplicationCoverBase_proper G X a m hm
  let f := multiplicationCoverBase G X a m
  let z := multiplicationCoverOrigin G X a O hO m
  let hz := multiplicationCoverOrigin_over G X a O hO m
  letI := descendedInclusion_closedImmersion f z hz
  obtain ⟨hf,he⟩ := abelian_cover_finite_etale G X a m hm
  letI := hf
  letI := he
  change IsFinite ((descendedOpen f z hz).ι ≫ pullback.fst a.left (multiplication G m)) ∧
    Etale ((descendedOpen f z hz).ι ≫ pullback.fst a.left (multiplication G m))
  exact ⟨inferInstance,inferInstance⟩

def multiplicationGeometricComponentOpen : (geometricScheme (multiplicationCoverBase G X a m)).Opens := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact geometricComponentOpen (multiplicationCoverBase G X a m) (multiplicationCoverOrigin G X a O hO m)
    (multiplicationCoverOrigin_over G X a O hO m)

def multiplicationComponentBaseChangeIso :
    pullback (multiplicationComponentToBase G X a O hO m hm) scalarExtension ≅
      (multiplicationGeometricComponentOpen G X a O hO m hm).toScheme := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact descendedComponentBaseChangeIso (multiplicationCoverBase G X a m) (multiplicationCoverOrigin G X a O hO m)
    (multiplicationCoverOrigin_over G X a O hO m)

theorem multiplicationComponent_geometric_connected :
    ConnectedSpace ↥(pullback (multiplicationComponentToBase G X a O hO m hm) scalarExtension : Scheme) := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact descendedComponent_geometric_connected _ _ _

theorem multiplicationComponent_proper : IsProper (multiplicationComponentToBase G X a O hO m hm) := by
  letI := multiplicationCoverBase_proper G X a m hm
  exact descendedComponent_proper _ _ _

theorem multiplicationComponent_curve [SmoothOfRelativeDimension 1 X.hom] :
    SmoothOfRelativeDimension 1 (multiplicationComponentToBase G X a O hO m hm) := by
  obtain ⟨_,he⟩ := multiplicationComponentProjection_finite_etale G X a O hO m hm
  letI := he
  have h : SmoothOfRelativeDimension (0+1) (multiplicationComponentProjection G X a O hO m hm ≫ X.hom) := inferInstance
  rw [multiplicationComponentProjection_over] at h
  exact h

/-- The geometric component is identified over the ORIGINAL cover and
hence over X, not only up to an abstract scheme isomorphism. -/
theorem multiplicationComponentBaseChangeIso_projection :
    (multiplicationComponentBaseChangeIso G X a O hO m hm).hom ≫
      (multiplicationGeometricComponentOpen G X a O hO m hm).ι ≫
      geometricProjection (multiplicationCoverBase G X a m) ≫ pullback.fst a.left (multiplication G m)=
    pullback.fst (multiplicationComponentToBase G X a O hO m hm) scalarExtension ≫
      multiplicationComponentProjection G X a O hO m hm := by
  letI := multiplicationCoverBase_proper G X a m hm
  have h := descendedComponentBaseChangeIso_projection (multiplicationCoverBase G X a m)
    (multiplicationCoverOrigin G X a O hO m) (multiplicationCoverOrigin_over G X a O hO m)
  have hh := congrArg (fun t : pullback (multiplicationComponentToBase G X a O hO m hm) scalarExtension ⟶ cover G X a m =>
    t ≫ pullback.fst a.left (multiplication G m)) h
  simpa only [multiplicationComponentBaseChangeIso,multiplicationGeometricComponentOpen,
    multiplicationComponentToBase,multiplicationComponentProjection,Category.assoc] using hh

/-- Exact algebraic portion of local survival: the literal multiplication
cover has an actual QQ-defined distinguished component, actual rational
origin, finite-etale projection, and actual geometric component base
change. The analytic local-point assertions are further theorems. -/
theorem actual_distinguished_multiplication_component :
    IsProper (multiplicationComponentToBase G X a O hO m hm) ∧
    IsFinite (multiplicationComponentProjection G X a O hO m hm) ∧
    Etale (multiplicationComponentProjection G X a O hO m hm) ∧
    (multiplicationComponentOrigin G X a O hO m hm ≫ multiplicationComponentToBase G X a O hO m hm=𝟙 qqBase) ∧
    (multiplicationComponentOrigin G X a O hO m hm ≫ multiplicationComponentProjection G X a O hO m hm=O.left) ∧
    Nonempty (pullback (multiplicationComponentToBase G X a O hO m hm) scalarExtension ≅
      (multiplicationGeometricComponentOpen G X a O hO m hm).toScheme) ∧
    ConnectedSpace ↥(pullback (multiplicationComponentToBase G X a O hO m hm) scalarExtension : Scheme) := by
  obtain ⟨hf,he⟩ := multiplicationComponentProjection_finite_etale G X a O hO m hm
  exact ⟨multiplicationComponent_proper G X a O hO m hm,hf,he,
    multiplicationComponentOrigin_over G X a O hO m hm,multiplicationComponentOrigin_projection G X a O hO m hm,
    ⟨multiplicationComponentBaseChangeIso G X a O hO m hm⟩,multiplicationComponent_geometric_connected G X a O hO m hm⟩

end FourCorner.ThetaLocalSurvival.ComponentDescent
