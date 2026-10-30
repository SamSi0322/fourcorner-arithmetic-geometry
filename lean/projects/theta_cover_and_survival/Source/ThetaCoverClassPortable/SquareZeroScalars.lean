import Mathlib.Algebra.TrivSqZeroExt.Basic

noncomputable section
set_option autoImplicit false
namespace FourCorner.ThetaLocalSurvival.SquareZeroScalars

def oppositeScalar : ℚᵐᵒᵖ →+* ℚ := (RingHom.id ℚ).fromOpposite (fun _ _ => Commute.all _ _)

scoped instance (priority := 2000) rightModule (M : Type) [AddCommGroup M] [Module ℚ M] :
    Module ℚᵐᵒᵖ M := Module.compHom M oppositeScalar

scoped instance (priority := 2000) central (M : Type) [AddCommGroup M] [Module ℚ M] :
    letI := rightModule M
    IsCentralScalar ℚ M := ⟨fun _ _ => rfl⟩

end FourCorner.ThetaLocalSurvival.SquareZeroScalars
