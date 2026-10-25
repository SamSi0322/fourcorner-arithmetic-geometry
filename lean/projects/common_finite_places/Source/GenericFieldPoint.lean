import Genus17Coordinates
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.GenericFieldPoint
variable {L : Type} [Field L] [Algebra ℚ L]

def pointOfEmbedding {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* L) : Spec (CommRingCat.of L) ⟶ M.C :=
  Spec.map (CommRingCat.ofHom (f.comp M.ffEquiv.symm.toRingHom)) ≫
    M.C.fromSpecStalk (genericPoint M.C)

/-- The explicit morphism is an R-valued point of the original Q-model. -/
theorem pointOfEmbedding_over {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* L) :
    pointOfEmbedding M f ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap ℚ L)) := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

theorem pointOfEmbedding_image {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* L) :
    pointOfEmbedding M f (IsLocalRing.closedPoint L) = genericPoint M.C := by
  change M.C.fromSpecStalk (genericPoint M.C)
    (Spec.map (CommRingCat.ofHom (f.comp M.ffEquiv.symm.toRingHom))
      (IsLocalRing.closedPoint L)) = _
  rw [Spec_closedPoint,Scheme.fromSpecStalk_closedPoint]

/-- Every actual regular section is evaluated by the field embedding.
This ties the rational-function coordinates to actual scheme-point pullback. -/
theorem pointOfEmbedding_section {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* L) (U : M.C.Opens) [Nonempty U]
    (s : Γ(M.C,U))
    (hx : pointOfEmbedding M f (IsLocalRing.closedPoint L) ∈ U) :
    (Scheme.stalkClosedPointTo (pointOfEmbedding M f)).hom
      (M.C.presheaf.germ U _ hx s) =
        f (M.ffEquiv.symm (M.C.germToFunctionField U s)) := by
  have h := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (X := M.C) (x := genericPoint M.C)
    (CommRingCat.ofHom (f.comp M.ffEquiv.symm.toRingHom)) U hx
  exact congrArg (fun g => (g : Γ(M.C,U) ⟶ CommRingCat.of L).hom s) h

/-- The assigned value of every original field coordinate is the value
of an actual regular section on an open neighbourhood of the scheme point. -/
theorem pointOfEmbedding_regular_value {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* L) (a : F) :
    ∃ (U : M.C.Opens) (hg : genericPoint M.C ∈ U)
      (hx : pointOfEmbedding M f (IsLocalRing.closedPoint L) ∈ U) (s : Γ(M.C,U)),
      M.C.presheaf.germ U (genericPoint M.C) hg s = M.ffEquiv a ∧
      (Scheme.stalkClosedPointTo (pointOfEmbedding M f)).hom
        (M.C.presheaf.germ U _ hx s) = f a := by
  obtain ⟨U,hg,s,hs⟩ := M.C.presheaf.exists_germ_eq (M.ffEquiv a)
  letI : Nonempty U := ⟨⟨genericPoint M.C,hg⟩⟩
  have hx : pointOfEmbedding M f (IsLocalRing.closedPoint L) ∈ U := by
    rw [pointOfEmbedding_image]; exact hg
  refine ⟨U,hg,hx,s,hs,?_⟩
  rw [pointOfEmbedding_section]
  change f (M.ffEquiv.symm (M.C.presheaf.germ U (genericPoint M.C) hg s)) = f a
  rw [hs,RingEquiv.symm_apply_apply]


end FourCorner.GenericFieldPoint
#print axioms FourCorner.GenericFieldPoint.pointOfEmbedding
#print axioms FourCorner.GenericFieldPoint.pointOfEmbedding_regular_value
