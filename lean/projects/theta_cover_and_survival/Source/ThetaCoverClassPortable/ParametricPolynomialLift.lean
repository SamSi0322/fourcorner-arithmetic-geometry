import ThetaCoverClassPortable.GeneratorPointEmbedding
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  {α β : Type*} (P : Algebra.Generators R A α)

/-- Actual substitution of the chosen base-algebra generators into the parameter variables. -/
def parameterSubstitution : MvPolynomial (α⊕β) R →ₐ[R] MvPolynomial β A :=
  aeval (Sum.elim (fun i => C (P.val i)) X)

theorem parameterSubstitution_rename (p : MvPolynomial α R) :
    parameterSubstitution R A (β:=β) P (rename Sum.inl p)=C (aeval P.val p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [parameterSubstitution]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
      simp only [map_mul,rename_X]
      rw [hp]
      simp [parameterSubstitution]

/-- Every actual polynomial over A has an actual polynomial lift over R in parameter coordinates. -/
theorem parameterSubstitution_surjective : Function.Surjective (parameterSubstitution R A (β:=β) P) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨rename Sum.inl (P.σ a),?_⟩
      rw [parameterSubstitution_rename,P.aeval_val_σ]
  | add p q hp hq =>
      obtain ⟨p',rfl⟩ := hp
      obtain ⟨q',rfl⟩ := hq
      exact ⟨p'+q',map_add _ _ _⟩
  | mul_X p i hp =>
      obtain ⟨p',rfl⟩ := hp
      refine ⟨p'*X (.inr i),?_⟩
      simp [parameterSubstitution]

theorem parameterSubstitution_pderiv (Q : MvPolynomial (α⊕β) R) (j : β) :
    parameterSubstitution R A (β:=β) P (pderiv (.inr j) Q) =
      pderiv j (parameterSubstitution R A (β:=β) P Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C r => simp [parameterSubstitution]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
      simp only [parameterSubstitution] at hp
      cases i with
      | inl i => simp [pderiv_mul,parameterSubstitution,pderiv_X,Pi.single_apply,hp]
      | inr i => simp [pderiv_mul,parameterSubstitution,pderiv_X,Pi.single_apply,hp,apply_ite]

variable (K : Type*) [CommRing K] [Algebra R K]

theorem parameterSubstitution_evaluation (φ : A →ₐ[R] K) (x : β→K)
    (Q : MvPolynomial (α⊕β) R) :
    eval₂ φ.toRingHom x (parameterSubstitution R A (β:=β) P Q) =
      eval₂ (algebraMap R K) (Sum.elim (generatorCoordinates R A K P φ) x) Q := by
  have h : (pointPolynomialEval R A K φ x).comp (parameterSubstitution R A (β:=β) P) =
      pointPolynomialEval R R K (Algebra.ofId R K)
        (Sum.elim (generatorCoordinates R A K P φ) x) := by
    ext i
    cases i <;> simp [pointPolynomialEval,parameterSubstitution,generatorCoordinates]
  exact congrArg (fun f => f Q) h

end FourCorner.ThetaLocalSurvival.StrongTopology
