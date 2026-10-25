import Slot02HighRatios
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Definitions.Def_AlgebraicCurve_CurveModelSmooth

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.ProjectiveLineCharts
universe u
variable (K : Type u) [Field K]
abbrev Ambient := MvPolynomial (Fin 2) K
abbrev grading := homogeneousSubmodule (Fin 2) K
abbrev P1 : Scheme := Proj (grading K)
abbrev member (i : Fin 2) : (X i : Ambient K) ∈ grading K 1 := Slot02HighProjSpace.X_mem_one K 1 i
abbrev chart (i : Fin 2) := Away (grading K) (X i)
abbrev other (i : Fin 2) : Fin 2 := Fin.rev i

def evalChart (i : Fin 2) : Ambient K →+* Polynomial K :=
  eval₂Hom Polynomial.C (fun j => if j=i then 1 else Polynomial.X)
def chartEval (i : Fin 2) : chart K i →+* Polynomial K :=
  (IsLocalization.Away.lift (S := Localization.Away (X i : Ambient K))
    (X i) (g := evalChart K i) (by simp [evalChart])).comp (algebraMap _ _)

lemma chartEval_mk (i : Fin 2) (n : ℕ) (p : Ambient K) (hp : p ∈ grading K (n • 1)) :
    chartEval K i (Away.mk (grading K) (member K i) n p hp) = evalChart K i p := by
  let l : Localization.Away (X i : Ambient K) →+* Polynomial K :=
    IsLocalization.Away.lift (X i) (g := evalChart K i) (by simp [evalChart])
  have h : l (Localization.mk p ⟨X i^n,⟨n,rfl⟩⟩) *
      l (algebraMap (Ambient K) (Localization.Away (X i : Ambient K)) (X i^n)) =
      l (algebraMap _ _ p) := by
    rw [← map_mul,Localization.mk_eq_mk',IsLocalization.mk'_spec]
  simpa [chartEval,l,IsLocalization.Away.lift_eq,evalChart] using h

lemma chartEval_ratio (i j : Fin 2) :
    chartEval K i (Slot02HighProjSpace.ratio K 1 i j) = if j=i then 1 else Polynomial.X := by
  rw [show Slot02HighProjSpace.ratio K 1 i j = Away.mk (grading K) (member K i) 1 (X j) _ from rfl,
    chartEval_mk]
  simp [evalChart]

lemma chartEval_constant (i : Fin 2) (a : K) :
    chartEval K i (algebraMap K (chart K i) a) = Polynomial.C a := by
  change chartEval K i (Away.mk (grading K) (member K i) 0 (C a) _) = _
  rw [chartEval_mk]
  simp [evalChart]

def chartInverse (i : Fin 2) : Polynomial K →+* chart K i :=
  Polynomial.eval₂RingHom (algebraMap K _) (Slot02HighProjSpace.ratio K 1 i (other i))

lemma chartEval_inverse (i : Fin 2) : (chartEval K i).comp (chartInverse K i) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,chartInverse,Polynomial.eval₂_C,Polynomial.coe_eval₂RingHom,RingHom.id_apply]
    change chartEval K i (algebraMap K _ a) = Polynomial.C a
    exact chartEval_constant K i a
  · simp only [RingHom.comp_apply,chartInverse,Polynomial.eval₂_X,Polynomial.coe_eval₂RingHom,RingHom.id_apply]
    change chartEval K i (Slot02HighProjSpace.ratio K 1 i (other i)) = Polynomial.X
    rw [chartEval_ratio]
    fin_cases i <;> simp [other]

lemma chartInverse_eval_ratio (i j : Fin 2) :
    chartInverse K i (chartEval K i (Slot02HighProjSpace.ratio K 1 i j)) = Slot02HighProjSpace.ratio K 1 i j := by
  rw [chartEval_ratio]
  fin_cases i <;> fin_cases j <;> simp [chartInverse,other,Slot02HighProjSpace.ratio_self]

lemma chartInverse_eval (i : Fin 2) : (chartInverse K i).comp (chartEval K i) = RingHom.id _ := by
  apply RingHom.ext
  intro z
  change chartInverse K i (chartEval K i z) = z
  have hz : z ∈ Algebra.adjoin K (Set.range (Slot02HighProjSpace.ratio K 1 i)) := by
    rw [Slot02HighProjSpace.adjoin_range_ratio]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨j,rfl⟩ := hx; exact chartInverse_eval_ratio K i j
  | algebraMap a => rw [chartEval_constant]; simp [chartInverse]
  | add x y hx hy hxe hye => simpa only [map_add] using congrArg₂ (·+·) hxe hye
  | mul x y hx hy hxe hye => simpa only [map_mul] using congrArg₂ (·*·) hxe hye

/-- Both actual standard projective-line charts have their genuine polynomial coordinate ring. -/
def chartEquiv (i : Fin 2) : chart K i ≃+* Polynomial K :=
  RingEquiv.ofRingHom (chartEval K i) (chartInverse K i) (chartEval_inverse K i) (chartInverse_eval K i)

def chartSchemeIso (i : Fin 2) :
    (Proj.basicOpen (grading K) (X i)).toScheme ≅ Spec (.of (Polynomial K)) :=
  Proj.basicOpenIsoSpec (grading K) (X i) (member K i) one_pos ≪≫
    Scheme.Spec.mapIso ((chartEquiv K i).symm.toCommRingCatIso.op)

end FourCorner.ProjectiveLineCharts
#print axioms FourCorner.ProjectiveLineCharts.chartEquiv
#print axioms FourCorner.ProjectiveLineCharts.chartSchemeIso
