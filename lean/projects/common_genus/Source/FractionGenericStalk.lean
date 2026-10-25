import NormalizationGenericPoint

noncomputable section
namespace FourCorner.FractionGenericStalk
open AlgebraicGeometry CategoryTheory
universe u
variable (R L : Type u) [CommRing R] [IsDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev fieldMap : Spec (.of L) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R L))

theorem fieldMap_generic : fieldMap R L (IsLocalRing.closedPoint L) = genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R L) (IsLocalRing.maximalIdeal L) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  apply le_antisymm ?_ bot_le
  intro a ha
  change algebraMap R L a = 0 at ha
  exact Ideal.mem_bot.mpr ((IsFractionRing.injective R L) (ha.trans (map_zero _).symm))

local instance stalkAlgebra (x : Spec (.of R)) : Algebra R ((Spec (.of R)).presheaf.stalk x) :=
  (StructureSheaf.toStalk R x).hom.toAlgebra

theorem stalk_eval_coeff (a : R) :
    Scheme.stalkClosedPointTo (fieldMap R L)
      (algebraMap R ((Spec (.of R)).presheaf.stalk (fieldMap R L (IsLocalRing.closedPoint L))) a) =
      algebraMap R L a := by
  have h : StructureSheaf.toStalk R (fieldMap R L (IsLocalRing.closedPoint L)) ≫
      Scheme.stalkClosedPointTo (fieldMap R L) = CommRingCat.ofHom (algebraMap R L) := by
    unfold Scheme.stalkClosedPointTo
    rw [← Category.assoc]
    erw [stalkMap_toStalk]
    rw [Category.assoc,
      ← stalkClosedPointIso_inv,Iso.inv_hom_id,Category.comp_id]
  exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of L => f a) h

/-- The actual generic-stalk evaluation of a fraction-field point is a field
isomorphism. Dominance alone is not used as a substitute for this assertion. -/
theorem stalk_eval_bijective : Function.Bijective (Scheme.stalkClosedPointTo (fieldMap R L)).hom := by
  haveI : IsFractionRing R ((Spec (.of R)).presheaf.stalk (fieldMap R L (IsLocalRing.closedPoint L))) := by
    rw [fieldMap_generic]
    exact functionField_isFractionRing_of_affine (.of R)
  let e := IsLocalization.algEquiv (nonZeroDivisors R) ((Spec (.of R)).presheaf.stalk (fieldMap R L (IsLocalRing.closedPoint L))) L
  have he : (Scheme.stalkClosedPointTo (fieldMap R L)).hom = e.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro a
    change Scheme.stalkClosedPointTo (fieldMap R L) (algebraMap R _ a) = e (algebraMap R _ a)
    rw [stalk_eval_coeff]
    exact (e.commutes a).symm
  rw [he]
  exact e.bijective

/-- Composition with an actual affine open immersion retains the generic-stalk
isomorphism, as do the normalization model's subsequent Scheme isomorphisms. -/
theorem open_stalk_eval_bijective {X : Scheme.{u}} (i : Spec (.of R) ⟶ X) [IsOpenImmersion i] :
    Function.Bijective (Scheme.stalkClosedPointTo (fieldMap R L ≫ i)).hom := by
  rw [Scheme.stalkClosedPointTo_comp]
  change Function.Bijective ((Scheme.stalkClosedPointTo (fieldMap R L)).hom.comp
    (i.stalkMap (fieldMap R L (IsLocalRing.closedPoint L))).hom)
  exact (stalk_eval_bijective R L).comp
    (asIso (i.stalkMap (fieldMap R L (IsLocalRing.closedPoint L)))).commRingCatIsoToRingEquiv.bijective

theorem open_fieldMap_generic {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of R) ⟶ X) [IsOpenImmersion i] :
    (fieldMap R L ≫ i) (IsLocalRing.closedPoint L) = genericPoint X := by
  change i (fieldMap R L (IsLocalRing.closedPoint L)) = _
  rw [fieldMap_generic]
  exact genericPoint_eq_of_isOpenImmersion i

end FourCorner.FractionGenericStalk
#print axioms FourCorner.FractionGenericStalk.stalk_eval_bijective

#print axioms FourCorner.FractionGenericStalk.open_stalk_eval_bijective
