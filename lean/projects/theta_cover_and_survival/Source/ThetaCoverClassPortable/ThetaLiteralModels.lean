import ThetaCoverClassPortable.ThetaProjectiveModel
import ThetaCoverClassPortable.ThetaProjectiveCoordinates
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 2000000
namespace FourCorner.ThetaLiteralModels
open MvPolynomial AlgebraicGeometry CategoryTheory
variable (k : Type*) [Field k]

def sourceEquation : Fin 3 → MvPolynomial (Fin 5) k
  | 0 => X 0^2-X 3^2-C 50*X 4^2
  | 1 => X 1^2-X 3^2-C 14*(X 3*X 4)-C 51*X 4^2
  | 2 => X 2^2-X 3^2+C 14*(X 3*X 4)-C 51*X 4^2
lemma source_homogeneous (a : Fin 3) : (sourceEquation k a).IsHomogeneous 2 := by
  fin_cases a
  · exact ((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).sub ((isHomogeneous_X_pow _ _).C_mul _)
  · exact (((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).sub
      (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).C_mul _)).sub
      ((isHomogeneous_X_pow _ _).C_mul _)
  · exact (((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).add
      (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).C_mul _)).sub
      ((isHomogeneous_X_pow _ _).C_mul _)

def targetPolynomial : MvPolynomial (Fin 3) k :=
  C 9801*(X 0^4+X 1^4)+C 19598*(X 0^2*X 1^2)-
    C 39592*((X 0^2+X 1^2)*X 2^2)+C 39984*X 2^4
def targetEquation (_ : Fin 1) := targetPolynomial k
lemma target_homogeneous (a : Fin 1) : (targetEquation k a).IsHomogeneous 4 := by
  have h2 (j : Fin 3) : (X j^2 : MvPolynomial (Fin 3) k).IsHomogeneous 2 := isHomogeneous_X_pow _ _
  have h4 (j : Fin 3) : (X j^4 : MvPolynomial (Fin 3) k).IsHomogeneous 4 := isHomogeneous_X_pow _ _
  have hxy : (X 0^2*X 1^2 : MvPolynomial (Fin 3) k).IsHomogeneous 4 := (h2 0).mul (h2 1)
  have hxz : ((X 0^2+X 1^2)*X 2^2 : MvPolynomial (Fin 3) k).IsHomogeneous 4 :=
    ((h2 0).add (h2 1)).mul (h2 2)
  exact (((((h4 0).add (h4 1)).C_mul _).add (hxy.C_mul _)).sub (hxz.C_mul _)).add ((h4 2).C_mul _)

/-- The literal intersection in P4 with ordered coordinates [P:Q:R:z:T]. -/
abbrev C := ThetaProjectiveModel.curve (sourceEquation k) (source_homogeneous k)
/-- The literal plane quartic in P2 with ordered coordinates [X:Y:Z]. -/
abbrev D := ThetaProjectiveModel.curve (targetEquation k) (target_homogeneous k)
abbrev cToBase := ThetaProjectiveModel.toBase (sourceEquation k) (source_homogeneous k)
abbrev dToBase := ThetaProjectiveModel.toBase (targetEquation k) (target_homogeneous k)
theorem c_proper : IsProper (cToBase k) := ThetaProjectiveModel.proper _ _
theorem d_proper : IsProper (dToBase k) := ThetaProjectiveModel.proper _ _
theorem c_closed : IsClosedImmersion
    (ThetaProjectiveModel.inclusion (sourceEquation k) (source_homogeneous k)) :=
  ThetaProjectiveModel.inclusion_closed _ _
theorem d_closed : IsClosedImmersion
    (ThetaProjectiveModel.inclusion (targetEquation k) (target_homogeneous k)) :=
  ThetaProjectiveModel.inclusion_closed _ _

lemma source_eval {L : Type*} [CommRing L] [Algebra k L] (x : Fin 5 → L) :
    (∀ a, MvPolynomial.aeval x (sourceEquation k a)=0) ↔
      x 0^2=x 3^2+50*x 4^2 ∧ x 1^2=x 3^2+14*x 3*x 4+51*x 4^2 ∧
        x 2^2=x 3^2-14*x 3*x 4+51*x 4^2 := by
  constructor
  · intro h
    have h0:=h 0;have h1:=h 1;have h2:=h 2
    simp [sourceEquation,map_ofNat] at h0 h1 h2
    exact ⟨by linear_combination h0,by linear_combination h1,by linear_combination h2⟩
  · rintro ⟨h0,h1,h2⟩ a
    fin_cases a <;> simp [sourceEquation,map_ofNat]
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2
lemma target_eval {L : Type*} [CommRing L] [Algebra k L] (x : Fin 3 → L) :
    MvPolynomial.aeval x (targetPolynomial k) =
      9801*(x 0^4+x 1^4)+19598*x 0^2*x 1^2-
      39592*(x 0^2+x 1^2)*x 2^2+39984*x 2^4 := by
  simp [targetPolynomial,map_ofNat];ring
end FourCorner.ThetaLiteralModels
#print axioms FourCorner.ThetaLiteralModels.c_proper
#print axioms FourCorner.ThetaLiteralModels.d_proper
#print axioms FourCorner.ThetaLiteralModels.source_eval
#print axioms FourCorner.ThetaLiteralModels.target_eval
