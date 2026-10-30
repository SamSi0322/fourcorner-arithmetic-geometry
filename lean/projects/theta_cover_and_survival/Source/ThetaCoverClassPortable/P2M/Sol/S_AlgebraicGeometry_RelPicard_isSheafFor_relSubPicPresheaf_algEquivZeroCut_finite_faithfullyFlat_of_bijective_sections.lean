import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_isSheafFor_relSubPicPresheaf_algEquivZeroCut_finite_faithfullyFlat_of_bijective_sections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra Opposite

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    (T : Over (Spec (CommRingCat.of R))) :
    Presieve.IsSheafFor (relSubPicPresheaf c ε (algEquivZeroCut c ε))
      (Presieve.singleton ((Over.mapPullbackAdj (SmoothProperCurve.specMap R R')).counit.app T)) := by
  classical
  rw [Presieve.isSheafFor_singleton]
  rintro ⟨ξ, hξ⟩ hx

  have hπ : ((Over.mapPullbackAdj (specMap R R')).counit.app T).left = pullback.fst T.hom (specMap R R') := by
    simp
  let πS : SchemeHomOver (pullback.snd T.hom (specMap R R') ≫ specMap R R') T.hom :=
    ⟨pullback.fst T.hom (specMap R R'), pullback.condition⟩

  set M' : RigidifiedLineBundle c ε (pullback.snd T.hom (specMap R R') ≫ specMap R R') := ξ.out with hM'def
  have hM' : Quotient.mk _ M' = ξ := Quotient.out_eq ξ
  have hξP : FibrewiseAlgEquivZero M' := by
    have h : (algEquivZeroCut c ε).onClasses _ ξ := hξ
    rw [← hM'] at h
    exact h

  have hcompat : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ p₂ : SchemeHomOver z (pullback.snd T.hom (specMap R R') ≫ specMap R R')),
      p₁.1 ≫ pullback.fst T.hom (specMap R R') = p₂.1 ≫ pullback.fst T.hom (specMap R R') →
        Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L) := by
    intro Z z p₁ p₂ hp
    let P₁ : Over.mk z ⟶ (Over.map (specMap R R')).obj ((Over.pullback (specMap R R')).obj T) :=
      Over.homMk p₁.1 p₁.2
    let P₂ : Over.mk z ⟶ (Over.map (specMap R R')).obj ((Over.pullback (specMap R R')).obj T) :=
      Over.homMk p₂.1 p₂.2
    have hP : P₁ ≫ (Over.mapPullbackAdj (specMap R R')).counit.app T =
        P₂ ≫ (Over.mapPullbackAdj (specMap R R')).counit.app T := by
      ext
      change p₁.1 ≫ ((Over.mapPullbackAdj (specMap R R')).counit.app T).left =
        p₂.1 ≫ ((Over.mapPullbackAdj (specMap R R')).counit.app T).left
      rw [hπ]
      exact hp
    have h := congrArg Subtype.val (hx P₁ P₂ hP)
    rw [relSubPicPresheaf_map_coe, relSubPicPresheaf_map_coe] at h
    change RigidifiedLineBundle.classesMap _ ξ = RigidifiedLineBundle.classesMap _ ξ at h
    rw [← hM'] at h
    exact Quotient.exact h

  obtain ⟨M, ⟨e⟩⟩ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_descent_finite_faithfullyFlat_of_bijective_sections
      R c ε hH0 R' T.hom M' hcompat

  have hM : FibrewiseAlgEquivZero M :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
      R c ε R' T.hom M ((algEquivZeroCut c ε).congr _ M' (M.pullbackAlong πS) ⟨e.symm⟩ hξP)

  have hmap : ∀ (ψ : SchemeHomOver (pullback.snd T.hom (specMap R R') ≫ specMap R R') T.hom),
      ψ.1 = pullback.fst T.hom (specMap R R') → ∀ N : RigidifiedLineBundle c ε T.hom,
        RigidifiedLineBundle.classesMap ψ (Quotient.mk _ N) = Quotient.mk _ (N.pullbackAlong πS) := by
    rintro ⟨ψ₁, hψ⟩ h N
    change ψ₁ = _ at h
    subst h
    rfl
  refine ⟨⟨Quotient.mk _ M, show (algEquivZeroCut c ε).onClasses T.hom (Quotient.mk _ M) from
    (SubPicCondition.onClasses_mk (algEquivZeroCut c ε) T.hom M).2 hM⟩, ?_, ?_⟩
  ·
    apply Subtype.ext
    rw [relSubPicPresheaf_map_coe]
    change RigidifiedLineBundle.classesMap _ (Quotient.mk _ M) = ξ
    rw [← hM']
    exact (hmap _ hπ M).trans (Quotient.sound ⟨e⟩)
  ·
    rintro ⟨ξ₁, hξ₁⟩ hy
    apply Subtype.ext
    change ξ₁ = Quotient.mk _ M
    obtain ⟨N, rfl⟩ := Quotient.exists_rep ξ₁
    have h₁ := congrArg Subtype.val hy
    rw [relSubPicPresheaf_map_coe] at h₁
    change RigidifiedLineBundle.classesMap _ (Quotient.mk _ N) = ξ at h₁
    have h₃ : Quotient.mk _ (N.pullbackAlong πS) = Quotient.mk _ M' :=
      ((hmap _ hπ N).symm.trans h₁).trans hM'.symm
    have h₂ : Nonempty ((N.pullbackAlong πS).L ≅ (M.pullbackAlong πS).L) :=
      ⟨(Quotient.exact h₃).some ≪≫ e.symm⟩
    exact Quotient.sound
      (AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
        R c ε hH0 R' T.hom N M h₂)
