import ThetaCoverClassPortable.ThetaQuotientChart
import ThetaCoverClassPortable.Slot02ProjectiveQuotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
noncomputable section
namespace FourCorner.ThetaProjectiveModel
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k] {n : ℕ} [NeZero n]
def ambientDegreeZeroEquiv : k ≃+* homogeneousSubmodule (Fin (n+1)) k 0 where
  toFun r := ⟨C r, isHomogeneous_C _ r⟩
  invFun p := constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    ext : 1
    have hp : p.1.IsHomogeneous 0 := p.2
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [constantCoeff]
    · rw [coeff_C, if_neg (Ne.symm hd)]
      by_contra h
      refine hd (Finsupp.ext fun j => ?_)
      have hdeg : Finsupp.weight (1 : Fin (n+1) → ℕ) d = 0 := hp (fun h0 => h h0.symm)
      simp only [Finsupp.weight_apply,Pi.one_apply,smul_eq_mul,mul_one,Finsupp.sum] at hdeg
      by_cases hj : j ∈ d.support
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hdeg j hj
      · exact Finsupp.notMem_support_iff.mp hj
  map_mul' a b := by ext : 1; simp
  map_add' a b := by ext : 1; simp

def ambientToSpec : Proj (homogeneousSubmodule (Fin (n+1)) k) ⟶ Spec (.of k) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (ambientDegreeZeroEquiv (n:=n)).toRingHom)

instance ambientFiniteType :
    Algebra.FiniteType (homogeneousSubmodule (Fin (n+1)) k 0) (ThetaAmbientChart.ambient k n) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (⟨C r,isHomogeneous_C _ r⟩ : homogeneousSubmodule (Fin (n+1)) k 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

theorem ambientToSpec_isProper : IsProper (ambientToSpec (k:=k) (n:=n)) := by
  unfold ambientToSpec
  haveI : IsProper (Proj.toSpecZero (homogeneousSubmodule (Fin (n+1)) k)) := inferInstance
  haveI : IsIso (CommRingCat.ofHom (ambientDegreeZeroEquiv (k:=k) (n:=n)).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ambientDegreeZeroEquiv.bijective
  haveI : IsIso (Spec.map (CommRingCat.ofHom (ambientDegreeZeroEquiv (k:=k) (n:=n)).toRingHom)) := inferInstance
  infer_instance


variable {ι : Type*} {d : ℕ} (q : ι → ThetaAmbientChart.ambient k n)
  (hq : ∀ i, (q i).IsHomogeneous d)
abbrev ideal := ThetaQuotientChart.homogeneousIdeal q hq
abbrev grading := ThetaQuotientChart.G q hq
abbrev curve := Proj (grading q hq)
abbrev coordinate (j : Fin (n+1)) := ThetaQuotientChart.quotientMap q hq (X j)
def inclusion : curve q hq ⟶ Proj (homogeneousSubmodule (Fin (n+1)) k) :=
  ProjectiveQuotient.quotientMap _ (ideal q hq)
theorem inclusion_closed : IsClosedImmersion (inclusion q hq) :=
  ProjectiveQuotient.quotientMap_isClosedImmersion _ _
def toBase : curve q hq ⟶ Spec (.of k) := inclusion q hq ≫ ambientToSpec
theorem proper : IsProper (toBase q hq) := by
  haveI := inclusion_closed q hq
  haveI : IsProper (ambientToSpec (k:=k) (n:=n)) := ambientToSpec_isProper
  unfold toBase
  infer_instance
abbrev affineRing (j : Fin (n+1)) := ThetaQuotientChart.affineRing q j
instance (j : Fin (n+1)) : Algebra k (affineRing q j) := Ideal.Quotient.algebra k
def chartIso (j : Fin (n+1)) :
    (Proj.basicOpen (grading q hq) (coordinate q hq j)).toScheme ≅ Spec (.of (affineRing q j)) :=
  ThetaQuotientChart.chartSchemeIso q hq j
lemma coordinate_degree (j : Fin (n+1)) : coordinate q hq j ∈ grading q hq 1 :=
  (ThetaQuotientChart.quotientMap q hq).map_mem (Slot02HighProjSpace.X_mem_one k n j)
lemma positive_mem {e : ℕ} (he : 0<e) (p : ThetaAmbientChart.ambient k n)
    (hp : p.IsHomogeneous e) : p ∈ Ideal.span (Set.range (X : Fin (n+1) → ThetaAmbientChart.ambient k n)) := by
  show p ∈ MvPolynomial.idealOfVars (Fin (n+1)) k
  rw [← pow_one (MvPolynomial.idealOfVars _ k), MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  rw [MvPolynomial.mem_support_iff] at hx
  have hdeg : Finsupp.degree x = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp hx
  omega
lemma irrelevant_span :
    (HomogeneousIdeal.irrelevant (grading q hq)).toIdeal ≤ Ideal.span (Set.range (coordinate q hq)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro e he a ha
  obtain ⟨p,hp,rfl⟩ := (mem_quotGrading_iff _ (ideal q hq).toIdeal).mp ha
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (ideal q hq).toIdeal) (positive_mem he p hp)
  change Ideal.Quotient.mk (ideal q hq).toIdeal p ∈
    Ideal.span (Set.range fun j : Fin (n+1) => Ideal.Quotient.mk (ideal q hq).toIdeal (X j))
  simpa only [Ideal.map_span,← Set.range_comp'] using hm
lemma opens_cover : ⨆ j : Fin (n+1), Proj.basicOpen (grading q hq) (coordinate q hq j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (irrelevant_span q hq)
end FourCorner.ThetaProjectiveModel
#print axioms FourCorner.ThetaProjectiveModel.proper
#print axioms FourCorner.ThetaProjectiveModel.chartIso
#print axioms FourCorner.ThetaProjectiveModel.opens_cover
