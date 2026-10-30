import ThetaCoverClassPortable.RationalComponentDescent
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.Connected.Clopen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace FourCorner.ThetaLocalSurvival.ComponentDescent
variable {Y : Scheme} (f : Y ⟶ qqBase)

/-- Actual categorical base change of an open subscheme. -/
def openScalarExtensionIso (U : Y.Opens) :
    pullback (U.ι ≫ f) scalarExtension ≅ (geometricProjection f ⁻¹ᵁ U).toScheme :=
  (pullbackRightPullbackFstIso f scalarExtension U.ι).symm ≪≫
    pullbackSymmetry U.ι (geometricProjection f) ≪≫
      pullbackRestrictIsoRestrict (geometricProjection f) U

def openScalarExtensionMap (U : Y.Opens) : pullback (U.ι ≫ f) scalarExtension ⟶ geometricScheme f :=
  (pullbackRightPullbackFstIso f scalarExtension U.ι).inv ≫
    pullback.snd U.ι (geometricProjection f)

@[reassoc (attr := simp)] theorem openScalarExtensionIso_hom_inclusion (U : Y.Opens) :
    (openScalarExtensionIso f U).hom ≫ (geometricProjection f ⁻¹ᵁ U).ι=openScalarExtensionMap f U := by
  simp only [openScalarExtensionIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι,pullbackSymmetry_hom_comp_fst]
  rfl

@[reassoc (attr := simp)] theorem openScalarExtensionMap_projection (U : Y.Opens) :
    openScalarExtensionMap f U ≫ geometricProjection f=
      pullback.fst (U.ι ≫ f) scalarExtension ≫ U.ι := by
  simp only [openScalarExtensionMap,geometricProjection,Category.assoc,pullbackRightPullbackFstIso_inv_snd_fst]

theorem opens_eqToIso_hom_inclusion {X : Scheme} {U V : X.Opens} (h : U=V) :
    (eqToIso (congrArg (fun W : X.Opens => W.toScheme) h)).hom ≫ V.ι=U.ι := by
  subst V
  exact Category.id_comp _

variable (O : qqBase ⟶ Y) (hO : O ≫ f=𝟙 qqBase) [IsProper f]

def descendedOpen : Y.Opens := Classical.choose (rational_origin_component_descends f O hO)

theorem descendedOpen_clopen : IsClopen (descendedOpen f O hO : Set Y) :=
  (Classical.choose_spec (rational_origin_component_descends f O hO)).1

theorem descendedOpen_preimage : geometricProjection f ⁻¹' (descendedOpen f O hO : Set Y)=
    connectedComponent (geometricOriginPoint f O hO) :=
  (Classical.choose_spec (rational_origin_component_descends f O hO)).2.1

theorem descendedOpen_origin : O (IsLocalRing.closedPoint ℚ)∈descendedOpen f O hO :=
  (Classical.choose_spec (rational_origin_component_descends f O hO)).2.2

theorem descendedOpen_preimage_open : geometricProjection f ⁻¹ᵁ descendedOpen f O hO=
    geometricComponentOpen f O hO := by
  apply TopologicalSpace.Opens.ext
  exact descendedOpen_preimage f O hO

/-- The descended object is a literal open subscheme over QQ. -/
abbrev descendedComponent : Scheme := (descendedOpen f O hO).toScheme
abbrev descendedToBase : descendedComponent f O hO ⟶ qqBase := (descendedOpen f O hO).ι ≫ f

/-- The base change of the actual QQ subscheme IS the actual geometric
connected component, by genuine categorical scheme isomorphisms. -/
def descendedComponentBaseChangeIso :
    pullback (descendedToBase f O hO) scalarExtension ≅ (geometricComponentOpen f O hO).toScheme :=
  openScalarExtensionIso f (descendedOpen f O hO) ≪≫
    eqToIso (congrArg (fun U : (geometricScheme f).Opens => U.toScheme) (descendedOpen_preimage_open f O hO))

@[reassoc (attr := simp)] theorem descendedComponentBaseChangeIso_inclusion :
    (descendedComponentBaseChangeIso f O hO).hom ≫ (geometricComponentOpen f O hO).ι=
      openScalarExtensionMap f (descendedOpen f O hO) := by
  unfold descendedComponentBaseChangeIso
  rw [Iso.trans_hom,Category.assoc,opens_eqToIso_hom_inclusion (descendedOpen_preimage_open f O hO)]
  exact openScalarExtensionIso_hom_inclusion f (descendedOpen f O hO)

/-- Explicit compatibility with the projection to the original QQ
scheme, so the isomorphism identifies the specified component as a
subscheme, rather than only an abstract isomorphism class. -/
theorem descendedComponentBaseChangeIso_projection :
    (descendedComponentBaseChangeIso f O hO).hom ≫ (geometricComponentOpen f O hO).ι ≫ geometricProjection f=
      pullback.fst (descendedToBase f O hO) scalarExtension ≫ (descendedOpen f O hO).ι := by
  rw [←Category.assoc,descendedComponentBaseChangeIso_inclusion,openScalarExtensionMap_projection]

/-- This is genuine connectedness of the literal Qbar base change. -/
theorem descendedComponent_geometric_connected :
    ConnectedSpace ↥(pullback (descendedToBase f O hO) scalarExtension : Scheme) := by
  have hC : ConnectedSpace (geometricComponentOpen f O hO).toScheme := by
    change ConnectedSpace (connectedComponent (geometricOriginPoint f O hO))
    exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  exact (descendedComponentBaseChangeIso f O hO).hom.homeomorph.connectedSpace_iff.mpr hC

theorem descendedComponent_connected : ConnectedSpace ↥(descendedComponent f O hO) := by
  letI : ConnectedSpace ↥(geometricScheme (descendedToBase f O hO)) :=
    descendedComponent_geometric_connected f O hO
  exact (geometricProjection_surjective (descendedToBase f O hO)).connectedSpace
    (geometricProjection (descendedToBase f O hO)).continuous

/-- The descended open is exactly the genuine QQ connected component
containing the rational origin, not an extra component designation. -/
theorem descendedOpen_eq_connectedComponent : (descendedOpen f O hO : Set Y)=
    connectedComponent (O (IsLocalRing.closedPoint ℚ)) := by
  have hU : _root_.IsConnected (descendedOpen f O hO : Set Y) :=
    isConnected_iff_connectedSpace.mpr (descendedComponent_connected f O hO)
  exact (hU.subset_connectedComponent (descendedOpen_origin f O hO)).antisymm
    ((descendedOpen_clopen f O hO).connectedComponent_subset (descendedOpen_origin f O hO))

theorem descendedOpen_origin_range : Set.range O⊆Set.range (descendedOpen f O hO).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x,rfl⟩
  rw [show x=IsLocalRing.closedPoint ℚ from Subsingleton.elim (α:=PrimeSpectrum ℚ) _ _]
  exact descendedOpen_origin f O hO

def descendedOrigin : qqBase ⟶ descendedComponent f O hO :=
  IsOpenImmersion.lift (descendedOpen f O hO).ι O (descendedOpen_origin_range f O hO)

@[reassoc (attr := simp)] theorem descendedOrigin_inclusion :
    descendedOrigin f O hO ≫ (descendedOpen f O hO).ι=O := IsOpenImmersion.lift_fac _ _ _

theorem descendedOrigin_over : descendedOrigin f O hO ≫ descendedToBase f O hO=𝟙 qqBase := by
  rw [descendedToBase,←Category.assoc,descendedOrigin_inclusion,hO]

theorem descendedInclusion_closedImmersion : IsClosedImmersion (descendedOpen f O hO).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (descendedOpen_clopen f O hO).isClosed

theorem descendedComponent_proper : IsProper (descendedToBase f O hO) := by
  letI := descendedInclusion_closedImmersion f O hO
  unfold descendedToBase
  infer_instance

theorem descendedComponent_smooth [Smooth f] : Smooth (descendedToBase f O hO) := by
  unfold descendedToBase
  infer_instance

/-- Full effective descent endpoint: actual QQ scheme, actual rational
origin, actual geometric connected-component isomorphism, and true
geometric connectedness at the algebraic closure. -/
theorem actual_rational_component_descent :
    IsProper (descendedToBase f O hO) ∧
    (descendedOrigin f O hO ≫ descendedToBase f O hO=𝟙 qqBase) ∧
    Nonempty (pullback (descendedToBase f O hO) scalarExtension ≅ (geometricComponentOpen f O hO).toScheme) ∧
    ConnectedSpace ↥(pullback (descendedToBase f O hO) scalarExtension : Scheme) :=
  ⟨descendedComponent_proper f O hO,descendedOrigin_over f O hO,
    ⟨descendedComponentBaseChangeIso f O hO⟩,descendedComponent_geometric_connected f O hO⟩

end FourCorner.ThetaLocalSurvival.ComponentDescent
