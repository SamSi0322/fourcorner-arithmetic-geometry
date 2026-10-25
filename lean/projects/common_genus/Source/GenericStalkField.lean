import FractionGenericStalk

noncomputable section
namespace FourCorner.GenericStalkField
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} [IsIntegral X] {L : Type u} [Field L]
    (f : Spec (.of L) ⟶ X) (hf : f (IsLocalRing.closedPoint L) = genericPoint X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo f).hom)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The field isomorphism is constructed from the actual morphism on stalks. -/
def equiv : X.functionField ≃+* L :=
  ((X.presheaf.stalkCongr (.of_eq hf.symm)).commRingCatIsoToRingEquiv).trans
    (RingEquiv.ofBijective (Scheme.stalkClosedPointTo f).hom hb)

/-- The supplied field point factors through the actual generic stalk by the
constructed field isomorphism, rather than an arbitrary field embedding. -/
theorem factor :
    Spec.map (CommRingCat.ofHom (equiv f hf hb).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) = f := by
  change Spec.map ((X.presheaf.stalkCongr (.of_eq hf.symm)).hom ≫ Scheme.stalkClosedPointTo f) ≫ _ = _
  rw [Spec.map_comp,Category.assoc]
  have hc : Spec.map (X.presheaf.stalkCongr (.of_eq hf.symm)).hom ≫
      X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (f (IsLocalRing.closedPoint L)) := by
    change Spec.map (X.presheaf.stalkSpecializes (Inseparable.of_eq hf.symm).ge) ≫ _ = _
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  rw [hc]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk f

end FourCorner.GenericStalkField
#print axioms FourCorner.GenericStalkField.equiv
#print axioms FourCorner.GenericStalkField.factor
