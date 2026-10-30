import ThetaCoverClassPortable.ThetaQQKummerLine
import ThetaCoverClassPortable.InvertibleRationalFiber

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
namespace FourCorner.ThetaQQRigidifiedLine
open ThetaLiteralModels ThetaQQKummerLine

def origin : SchemeHomOver (𝟙 (Spec (.of ℚ))) (dToBase ℚ) :=
  ⟨ThetaCoverRationalData.rationalPoint (true,true),ThetaCoverRationalData.rationalPoint_over (true,true)⟩

/-- A genuine QQ basis in the fibre at the original rational O_D. -/
def originFiberBasis :
    (Scheme.Modules.pullback origin.val).obj L ≅
      SheafOfModules.unit (Spec (.of ℚ)).ringCatSheaf :=
  InvertibleRationalFiber.basis origin.val L L_invertible

def relativeLine : (pullback (dToBase ℚ) (𝟙 (Spec (.of ℚ)))).Modules :=
  (Scheme.Modules.pullback (pullback.fst (dToBase ℚ) (𝟙 _))).obj L

lemma rigSection_fst :
    RelPicard.rigSection (dToBase ℚ) (𝟙 _) origin ≫ pullback.fst (dToBase ℚ) (𝟙 _)=origin.val := by
  simp only [RelPicard.rigSection,pullback.lift_fst,Category.id_comp]

/-- The actual relative-Picard input, with a true fibre trivialization.
No fixed-Galois-class descent or represented-Jacobian placeholder is used. -/
def rigidifiedLine : RelPicard.RigidifiedLineBundle (dToBase ℚ) origin (𝟙 (Spec (.of ℚ))) where
  L := relativeLine
  isInvertible := L_invertible.pullback _
  rigidified := ⟨(Scheme.Modules.pullbackComp (RelPicard.rigSection (dToBase ℚ) (𝟙 _) origin)
      (pullback.fst (dToBase ℚ) (𝟙 _))).app L ≪≫
    (Scheme.Modules.pullbackCongr rigSection_fst).app L ≪≫ originFiberBasis⟩

#print axioms originFiberBasis
#print axioms rigidifiedLine
end FourCorner.ThetaQQRigidifiedLine
