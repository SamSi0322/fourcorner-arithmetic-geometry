import OrderedSourceDominance
import IntegralEvaluationInjection
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource
open Polynomial

/-- The literal two-variable polynomial coefficient ring embeds in the ordinary
multivariable polynomial ring with its x,y order retained. -/
def coefficientToMv : OriginalTower.Coeff →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  Polynomial.aevalTower (Polynomial.aeval (MvPolynomial.X 0)) (MvPolynomial.X 1)
def mvToCoefficient : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] OriginalTower.Coeff :=
  MvPolynomial.aeval ![OriginalTower.x,OriginalTower.y]

theorem coefficientToMv_left_inverse :
    mvToCoefficient.comp coefficientToMv=AlgHom.id ℚ OriginalTower.Coeff := by
  apply AlgHom.coe_ringHom_injective
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp [coefficientToMv,mvToCoefficient,Polynomial.aevalTower]
    · simp [coefficientToMv,mvToCoefficient,Polynomial.aevalTower,OriginalTower.x]
  · simp [coefficientToMv,mvToCoefficient,Polynomial.aevalTower,OriginalTower.y]

theorem coefficientToMv_injective : Function.Injective coefficientToMv := by
  intro p q hpq
  have hh := congrArg mvToCoefficient hpq
  change (mvToCoefficient.comp coefficientToMv) p=(mvToCoefficient.comp coefficientToMv) q at hh
  simpa only [coefficientToMv_left_inverse,AlgHom.id_apply] using hh

/-- The actual source evaluation of the independently presented four-root tower. -/
def towerEvaluation (n : ℚ) (hn : n≠0) : OriginalTower.Ring →ₐ[ℚ] sourceField n :=
  (originalCoordinateMap n hn).comp OriginalTower.fromTower

theorem coefficient_evaluation (n : ℚ) (hn : n≠0) :
    (towerEvaluation n hn).toRingHom.comp (algebraMap OriginalTower.Coeff OriginalTower.Ring)=
      ((MvPolynomial.aeval (returnedXY n)).comp coefficientToMv).toRingHom := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext r
      simp [towerEvaluation,coefficientToMv,Polynomial.aevalTower]
    · change originalCoordinateMap n hn (OriginalTower.fromTower
        (algebraMap OriginalTower.Coeff OriginalTower.Ring OriginalTower.x))=_
      rw [OriginalTower.fromTower_coeff,OriginalTower.coeffReturn_x]
      simp [originalCoordinateMap,coefficientToMv,Polynomial.aevalTower,returnedXY]
  · change originalCoordinateMap n hn (OriginalTower.fromTower
      (algebraMap OriginalTower.Coeff OriginalTower.Ring OriginalTower.y))=_
    rw [OriginalTower.fromTower_coeff,OriginalTower.coeffReturn_y]
    simp [originalCoordinateMap,coefficientToMv,Polynomial.aevalTower,returnedXY]

theorem towerEvaluation_injective (n : ℚ) (hn : n≠0) : Function.Injective (towerEvaluation n hn) := by
  letI : Module.Finite OriginalTower.Third OriginalTower.Ring :=
    (monic_X_pow_sub_C (algebraMap OriginalTower.Coeff OriginalTower.Third (OriginalTower.radicand 3))
      (by decide : 2≠0)).finite_adjoinRoot
  letI : Module.Finite OriginalTower.Coeff OriginalTower.Ring :=
    Module.Finite.trans (R:=OriginalTower.Coeff) OriginalTower.Third OriginalTower.Ring
  apply FourCorner.IntegralEvaluationInjection.injective_of_base (R:=OriginalTower.Coeff)
    (towerEvaluation n hn).toRingHom
  rw [coefficient_evaluation n hn]
  intro p q hpq
  apply coefficientToMv_injective
  exact (returnedXY_independent n hn) hpq

/-- Genuine injectivity on the literal original four-distance quotient, with no extra premise. -/
theorem originalCoordinateMap_injective (n : ℚ) (hn : n≠0) :
    Function.Injective (originalCoordinateMap n hn) := by
  intro p q hpq
  apply OriginalTower.equiv.injective
  apply towerEvaluation_injective n hn
  change originalCoordinateMap n hn (OriginalTower.fromTower (OriginalTower.toTower p))=
    originalCoordinateMap n hn (OriginalTower.fromTower (OriginalTower.toTower q))
  have hh := OriginalTower.original_comp
  have hp := AlgHom.congr_fun hh p
  have hq := AlgHom.congr_fun hh q
  change OriginalTower.fromTower (OriginalTower.toTower p)=p at hp
  change OriginalTower.fromTower (OriginalTower.toTower q)=q at hq
  rw [hp,hq]; exact hpq

/-- The genuine fraction-field embedding of the literal four-distance surface into X_n. -/
def originalFieldEmbedding (n : ℚ) (hn : n≠0) : OriginalFunctionField →ₐ[ℚ] sourceField n :=
  IsFractionRing.liftAlgHom (originalCoordinateMap_injective n hn)

@[simp] theorem originalFieldEmbedding_coordinates (n : ℚ) (hn : n≠0) (i : Fin 6) :
    originalFieldEmbedding n hn (fieldCoordinates i)=originalImage n i := by
  change IsFractionRing.lift (originalCoordinateMap_injective n hn)
    (algebraMap OriginalRing OriginalFunctionField (originalCoordinates i))=_
  rw [IsFractionRing.lift_algebraMap]
  exact originalLift_coordinate _ _ _

#print axioms originalCoordinateMap_injective
#print axioms originalFieldEmbedding
#print axioms originalFieldEmbedding_coordinates
end FourCorner.OriginalCoverCompletion.OrderedSource
