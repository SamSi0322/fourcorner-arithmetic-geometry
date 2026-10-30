import ThetaLocalSurvivalPortable.EtaleSquarePresentation
import ThetaLocalSurvivalPortable.ImplicitGraphChart

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open MvPolynomial
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (A S K : Type) [CommRing A] [CommRing S] [Algebra ℚ A]
  [Algebra A S] [Algebra ℚ S] [IsScalarTower ℚ A S]
  [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K]
  {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
  (G : Algebra.Generators ℚ A α) (P : Algebra.SubmersivePresentation A S β β)

/-- Genuine QQ-polynomial lifts of the genuine presentation relations. -/
def liftedRelation (i : β) : MvPolynomial (α⊕β) ℚ :=
  (parameterSubstitution_surjective ℚ A G (P.relation i)).choose

theorem liftedRelation_spec (i : β) :
    parameterSubstitution ℚ A G (liftedRelation A S G P i)=P.relation i :=
  (parameterSubstitution_surjective ℚ A G (P.relation i)).choose_spec

def analyticRelation (i : β) : MvPolynomial (α⊕β) K :=
  MvPolynomial.map (algebraMap ℚ K) (liftedRelation A S G P i)

theorem polynomialSystem_actual_equations (φ : A →ₐ[ℚ] K) (x : β→K) :
    polynomialSystem (analyticRelation A S K G P) (generatorCoordinates ℚ A K G φ,x)=
      fun i => eval₂ φ.toRingHom x (P.relation i) := by
  funext i
  change eval (Sum.elim (generatorCoordinates ℚ A K G φ) x)
    (MvPolynomial.map (algebraMap ℚ K) (liftedRelation A S G P i)) = _
  rw [←eval₂_eq_eval_map,←parameterSubstitution_evaluation ℚ A G K φ x,
    liftedRelation_spec]

def actualPresentationBase (f : S →ₐ[ℚ] K) : A →ₐ[ℚ] K := f.comp (Algebra.algHom ℚ A S)
def actualPresentationVariables (f : S →ₐ[ℚ] K) : β→K := fun i=>f (P.val i)

theorem eval₂_actual_point (f : S →ₐ[ℚ] K) (p : MvPolynomial β A) :
    eval₂ (actualPresentationBase A S K f).toRingHom
      (actualPresentationVariables A S K P f) p = f (aeval P.val p) := by
  rw [aeval_def]
  change _ = f.toRingHom (eval₂ (algebraMap A S) P.val p)
  rw [eval₂_comp_left]
  rfl

theorem polynomialSystem_actual_point_zero (f : S →ₐ[ℚ] K) :
    polynomialSystem (analyticRelation A S K G P)
      (generatorCoordinates ℚ A K G (actualPresentationBase A S K f),
        actualPresentationVariables A S K P f)=0 := by
  rw [polynomialSystem_actual_equations]
  funext i
  exact eval₂_point_relation ℚ A K S P.toPresentation f i

theorem polynomialUnknownJacobian_actual_point (f : S →ₐ[ℚ] K) :
    polynomialUnknownJacobian (analyticRelation A S K G P)
      (generatorCoordinates ℚ A K G (actualPresentationBase A S K f),
        actualPresentationVariables A S K P f)=evaluatedPresentationJacobian P f := by
  ext i j
  change eval (Sum.elim (generatorCoordinates ℚ A K G (actualPresentationBase A S K f))
    (actualPresentationVariables A S K P f))
    (pderiv (.inr j) (MvPolynomial.map (algebraMap ℚ K) (liftedRelation A S G P i))) = _
  rw [pderiv_map,←eval₂_eq_eval_map,←parameterSubstitution_evaluation ℚ A G K,
    parameterSubstitution_pderiv,liftedRelation_spec]
  exact eval₂_actual_point A S K P f _

/-- An actual ambient analytic chart for every actual field-valued point of a square etale
presentation, obtained by proving its explicit evaluated Jacobian invertible. -/
theorem actual_presentation_implicit_chart (hP : P.map=id) (f : S →ₐ[ℚ] K) :
    ∃ e : OpenPartialHomeomorph ((α→K)×(β→K)) ((β→K)×(α→K)),
      (generatorCoordinates ℚ A K G (actualPresentationBase A S K f),
        actualPresentationVariables A S K P f)∈e.source ∧
      ∀ w, e w=(polynomialSystem (analyticRelation A S K G P) w,w.1) := by
  let u := (generatorCoordinates ℚ A K G (actualPresentationBase A S K f),
    actualPresentationVariables A S K P f)
  have hd := hasStrictFDerivAt_polynomialSystem (analyticRelation A S K G P) u
  have hj : (polynomialUnknownJacobian (analyticRelation A S K G P) u).det≠0 := by
    rw [polynomialUnknownJacobian_actual_point A S K G P f]
    exact evaluatedPresentationJacobian_det_ne_zero P hP f
  have hi : (polynomialSystemDerivative (analyticRelation A S K G P) u ∘L
      ContinuousLinearMap.inr K (α→K) (β→K)).IsInvertible := by
    rw [polynomialSystemDerivative_inr]
    exact matrixCLM_isInvertible _ hj
  let data := hd.implicitFunctionDataOfProdDomain hi
  refine ⟨data.toOpenPartialHomeomorph,data.pt_mem_toOpenPartialHomeomorph_source,?_⟩
  intro w
  exact data.toOpenPartialHomeomorph_apply w

end FourCorner.ThetaLocalSurvival.StrongTopology
