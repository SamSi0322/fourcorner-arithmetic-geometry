import ThetaCoverClassPortable.ActualFGModel
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.RelPicard.LFP
namespace FourCorner.ActualFGModel

/-- Direct interface for the already proper actual fixed curve. -/
theorem exists_rigidified_fg_model_of_isProper
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (L : RigidifiedLineBundle c ε (specMap R A)) :
    ∃ (D : Subalgebra R A), D.FG ∧
      ∃ (L0 : RigidifiedLineBundle c ε (specMap R ↥D)),
        Nonempty ((L0.pullbackAlong (stageHom R D.val)).L ≅ L.L) :=
  exists_rigidified_fg_model R c ε A L

theorem isLFPSurj_relPicardPresheaf_of_isProper
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPSurj (relPicardPresheaf c ε) :=
  isLFPSurj_relPicardPresheaf R c ε

end FourCorner.ActualFGModel
