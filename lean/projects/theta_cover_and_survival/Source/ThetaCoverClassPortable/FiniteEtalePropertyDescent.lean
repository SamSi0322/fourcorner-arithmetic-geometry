import ThetaCoverClassPortable.SmoothFlatDescent
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.FiniteEtalePropertyDescent

/-- Separatedness can be tested by universal closedness of the actual diagonal,
since the diagonal of every scheme morphism is an immersion. -/
theorem separated_iff_diagonal_universallyClosed {X S : Scheme.{u}} (f : X ⟶ S) :
    AlgebraicGeometry.IsSeparated f ↔
      AlgebraicGeometry.UniversallyClosed (pullback.diagonal f) := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    constructor
    apply AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion
    simpa only [Set.image_univ] using
      (pullback.diagonal f).isClosedMap Set.univ isClosed_univ

/-- Geometric connectedness descends along every surjective base change. The
residue field of a point over each field-valued base point gives an actual field
extension, and its fibre maps continuously and surjectively onto the old fibre. -/
theorem geometricallyConnected_of_surjective_baseChange
    {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (s : S' ⟶ S)
    [AlgebraicGeometry.Surjective s]
    [AlgebraicGeometry.GeometricallyConnected (pullback.snd f s)] :
    AlgebraicGeometry.GeometricallyConnected f := by
  classical
  constructor
  apply (AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X) (f := f)).mpr
  intro K _ x
  let T := pullback s x
  haveI : Nonempty T := by
    obtain ⟨z, _⟩ := (pullback.snd s x).surjective (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  let z : T := Classical.choice inferInstance
  let a := T.fromSpecResidueField z
  let y := a ≫ pullback.fst s x
  let j := a ≫ pullback.snd s x
  have hj : j ≫ x = y ≫ s := by
    dsimp only [j, y]
    rw [Category.assoc, Category.assoc, pullback.condition]
  haveI : AlgebraicGeometry.Surjective j := inferInstance
  let e : pullback (pullback.snd f s) y ≅ pullback (pullback.snd f x) j :=
    pullbackLeftPullbackSndIso f s y ≪≫
      pullback.congrHom rfl hj.symm ≪≫ (pullbackLeftPullbackSndIso f x j).symm
  haveI : ConnectedSpace ↥(pullback (pullback.snd f s) y : Scheme.{u}) :=
    AlgebraicGeometry.GeometricallyConnected.geometrically_connectedSpace
      y (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)
  haveI : ConnectedSpace ↥(pullback (pullback.snd f x) j : Scheme.{u}) :=
    e.hom.homeomorph.surjective.connectedSpace e.hom.continuous
  exact (pullback.fst (pullback.snd f x) j).surjective.connectedSpace
    (pullback.fst (pullback.snd f x) j).continuous

/-- Universal closedness of the diagonal gives separated fpqc descent. -/
theorem separated_descendsAlong :
    MorphismProperty.DescendsAlong @IsSeparated
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have hEq : @IsSeparated = MorphismProperty.diagonal @UniversallyClosed := by
    ext X S f
    exact separated_iff_diagonal_universallyClosed f
  rw [hEq]
  infer_instance

/-- The three properties are descended on the same actual base-change
isomorphism returned by effective representation descent. -/
theorem properties_of_baseChange_iso
    {X S S' X' : Scheme.{u}} (f : X ⟶ S) (s : S' ⟶ S) (f' : X' ⟶ S')
    [Surjective s] [Flat s] [QuasiCompact s]
    (e : pullback f s ≅ X') (he : e.hom ≫ f' = pullback.snd f s)
    (hsm : Smooth f') (hpr : IsProper f') (hgc : GeometricallyConnected f') :
    Smooth f ∧ IsProper f ∧ GeometricallyConnected f := by
  haveI : Smooth (pullback.snd f s) := by
    rw [←he, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)]
    exact hsm
  haveI : IsProper (pullback.snd f s) := by
    rw [←he, MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
    exact hpr
  haveI : GeometricallyConnected (pullback.snd f s) := by
    rw [←he, MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)]
    exact hgc
  haveI := smooth_descendsAlong
  haveI := separated_descendsAlong
  haveI : Smooth f := MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := s)
    ⟨⟨inferInstance,inferInstance⟩,inferInstance⟩ inferInstance
  haveI : IsSeparated f := MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := s)
    ⟨⟨inferInstance,inferInstance⟩,inferInstance⟩ inferInstance
  haveI : UniversallyClosed f := MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := s)
    ⟨⟨inferInstance,inferInstance⟩,inferInstance⟩ inferInstance
  exact ⟨inferInstance, ⟨⟩, geometricallyConnected_of_surjective_baseChange f s⟩

end FourCorner.FiniteEtalePropertyDescent
