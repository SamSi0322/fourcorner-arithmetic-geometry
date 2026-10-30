import ThetaCoverClassPortable.FiniteEtalePropertyDescent
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite
universe u
namespace FourCorner.FiniteEtalePicardAssembly

/-- Typed assembly of actual Picard representation descent. The finite-FF class
sheaf and AF input remain explicit here and are discharged by the curve-specific
wrapper only after their genuine constructions are available. -/
theorem of_singleton_sheaf
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    (hG : ∀ T : Over (Spec (CommRingCat.of R)),
      Presieve.IsSheafFor (relSubPicPresheaf c ε (algEquivZeroCut c ε))
        (Presieve.singleton ((Over.mapPullbackAdj (specMap R R')).counit.app T)))
    (D' : RelativePic0Designation R' (baseChange R c R'))
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) D')
    (hsm : Smooth D'.toBase) (hpr : IsProper D'.toBase)
    (hgc : GeometricallyConnected D'.toBase)
    (haff : ∀ S : Finset D'.P, ∃ U : D'.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        ∃ e : pullback D.toBase (specMap R R') ≅ D'.P,
          e.hom ≫ D'.toBase = pullback.snd D.toBase (specMap R R') := by
  have hrep' := BaseChange.representableByRestrict c ε R' h'
  obtain ⟨X, f, rep, e, he⟩ :=
    AlgebraicGeometry.exists_representableBy_of_representableBy_restrict_finiteEtale
      R R' (relSubPicPresheaf c ε (algEquivZeroCut c ε)) hG D'.toBase hrep' haff
  have hflatSurj : Flat (specMap R R') ∧ Surjective (specMap R R') :=
    (flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  haveI := hflatSurj.1
  haveI := hflatSurj.2
  obtain ⟨hs,hp,hg⟩ := FiniteEtalePropertyDescent.properties_of_baseChange_iso
    f (specMap R R') D'.toBase e he hsm hpr hgc
  let u₀ : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj
      (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :=
    ⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), (algEquivZeroCut c ε).unit_mem (𝟙 _)⟩
  let z : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk f := rep.homEquiv.symm u₀
  let D : RelativePic0Designation R c :=
    { P := X, toBase := f, zeroSection := z.left, zeroSection_toBase := Over.w z }
  have hz : (Over.homMk D.zeroSection D.zeroSection_toBase :
      Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase) = z :=
    Over.OverMorphism.ext rfl
  have h0 : (rep.homEquiv (Over.homMk D.zeroSection D.zeroSection_toBase :
      Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)) := by
    rw [hz]
    change (rep.homEquiv (rep.homEquiv.symm u₀)).1 = _
    rw [Equiv.apply_symm_apply]
  exact ⟨D,RepresentsRelSubPic.nonempty_of_representableBy rep h0,hs,hp,hg,e,he⟩

end FourCorner.FiniteEtalePicardAssembly
