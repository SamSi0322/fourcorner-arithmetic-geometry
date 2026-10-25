import RealFieldEmbedding08
import ProperCommonExclusion07
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ActualRealPoint08
open CommonLiteralField RealFieldEmbedding08

def pointOfEmbedding {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* ℝ) : Spec (CommRingCat.of ℝ) ⟶ M.C :=
  Spec.map (CommRingCat.ofHom (f.comp M.ffEquiv.symm.toRingHom)) ≫
    M.C.fromSpecStalk (genericPoint M.C)

/-- The explicit morphism is an R-valued point of the original Q-model. -/
theorem pointOfEmbedding_over {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* ℝ) :
    pointOfEmbedding M f ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

theorem pointOfEmbedding_image {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* ℝ) :
    pointOfEmbedding M f (IsLocalRing.closedPoint ℝ) = genericPoint M.C := by
  change M.C.fromSpecStalk (genericPoint M.C)
    (Spec.map (CommRingCat.ofHom (f.comp M.ffEquiv.symm.toRingHom))
      (IsLocalRing.closedPoint ℝ)) = _
  rw [Spec_closedPoint,Scheme.fromSpecStalk_closedPoint]

/-- Every actual regular section is evaluated by the field embedding.
This ties the rational-function coordinates to actual scheme-point pullback. -/
theorem pointOfEmbedding_section {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* ℝ) (U : M.C.Opens) [Nonempty U]
    (s : Γ(M.C,U))
    (hx : pointOfEmbedding M f (IsLocalRing.closedPoint ℝ) ∈ U) :
    (Scheme.stalkClosedPointTo (pointOfEmbedding M f)).hom
      (M.C.presheaf.germ U _ hx s) =
        f (M.ffEquiv.symm (M.C.germToFunctionField U s)) := by
  have h := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (X := M.C) (x := genericPoint M.C)
    (CommRingCat.ofHom (f.comp M.ffEquiv.symm.toRingHom)) U hx
  exact congrArg (fun g => (g : Γ(M.C,U) ⟶ CommRingCat.of ℝ).hom s) h

/-- The assigned value of every original field coordinate is the value
of an actual regular section on an open neighbourhood of the scheme point. -/
theorem pointOfEmbedding_regular_value {F : Type*} [Field F] [Algebra ℚ F]
    (M : CurveModel ℚ F) (f : F →+* ℝ) (a : F) :
    ∃ (U : M.C.Opens) (hg : genericPoint M.C ∈ U)
      (hx : pointOfEmbedding M f (IsLocalRing.closedPoint ℝ) ∈ U) (s : Γ(M.C,U)),
      M.C.presheaf.germ U (genericPoint M.C) hg s = M.ffEquiv a ∧
      (Scheme.stalkClosedPointTo (pointOfEmbedding M f)).hom
        (M.C.presheaf.germ U _ hx s) = f a := by
  obtain ⟨U,hg,s,hs⟩ := M.C.presheaf.exists_germ_eq (M.ffEquiv a)
  letI : Nonempty U := ⟨⟨genericPoint M.C,hg⟩⟩
  have hx : pointOfEmbedding M f (IsLocalRing.closedPoint ℝ) ∈ U := by
    rw [pointOfEmbedding_image]; exact hg
  refine ⟨U,hg,hx,s,hs,?_⟩
  rw [pointOfEmbedding_section]
  change f (M.ffEquiv.symm (M.C.presheaf.germ U (genericPoint M.C) hg s)) = f a
  rw [hs,RingEquiv.symm_apply_apply]

/-- The strict ordered field source is realized on the same genuine proper
Q-model, and all five coordinates are preserved by the actual generic-stalk
factorization. -/
theorem strict_real_point08 {t : ℚ} (ht : 1<t) (htop : (t:ℝ)<Real.sqrt 5/2)
    (M : CurveModel ℚ (field ℚ t)) :
    ∃ (S : CommonRootSource ℝ (t:ℝ)) (f : field ℚ t →+* ℝ)
      (p : Spec (CommRingCat.of ℝ) ⟶ M.C),
      p ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) ∧
      p = Spec.map (CommRingCat.ofHom (f.comp M.ffEquiv.symm.toRingHom)) ≫
        M.C.fromSpecStalk (genericPoint M.C) ∧
      f (ell ℚ t) = S.ell ∧ (∀ k, f (root ℚ t k) = sourceRoots S k) ∧
      (t:ℝ)-1 < S.ell ∧ S.ell < (t:ℝ)+1 ∧ 0<S.P ∧ 0<S.B ∧
        |S.P*S.M|+|S.B*S.C|<2 := by
  obtain ⟨S,he,hs,hT,hP,hB,hret⟩ := real_transcendental_source08 (by exact_mod_cast ht) htop
  let f := embedding t ht S he
  exact ⟨S,f,pointOfEmbedding M f,pointOfEmbedding_over M f,rfl,
    embedding_ell t ht S he,embedding_root t ht S he,hs,hT,hP,hB,hret⟩

#print axioms pointOfEmbedding
#print axioms pointOfEmbedding_over
#print axioms pointOfEmbedding_image
#print axioms pointOfEmbedding_section
#print axioms pointOfEmbedding_regular_value
#print axioms strict_real_point08
end FourCorner.ActualRealPoint08
