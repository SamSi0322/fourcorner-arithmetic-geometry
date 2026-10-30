import ProjectiveLineCharts
import IntegralTwoOpen

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.ProjectiveLineCharts
universe u
variable (K : Type u) [Field K]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def toBase : P1 K ⟶ Spec (.of K) :=
  Proj.toSpecZero (grading K) ≫ Spec.map (CommRingCat.ofHom (Slot02HighProjSpace.grad0Equiv K 1).toRingHom)

instance ambientFiniteType : Algebra.FiniteType (grading K 0) (Ambient K) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X,eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C a => exact Subalgebra.algebraMap_mem _ (⟨C a,isHomogeneous_C _ a⟩ : grading K 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

lemma proper : IsProper (toBase K) := by
  unfold toBase
  haveI : IsIso (CommRingCat.ofHom (Slot02HighProjSpace.grad0Equiv K 1).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (Slot02HighProjSpace.grad0Equiv K 1).bijective
  infer_instance

lemma away_over (i : Fin 2) :
    Proj.awayι (grading K) (X i) (member K i) one_pos ≫ toBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (chart K i))) := by
  unfold toBase
  rw [← Category.assoc,Proj.awayι_toSpecZero,← Spec.map_comp]
  rfl

lemma chart_over (i : Fin 2) :
    (chartSchemeIso K i).inv ≫ (Proj.basicOpen (grading K) (X i)).ι ≫ toBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
  change Spec.map (CommRingCat.ofHom (chartEquiv K i).toRingHom) ≫
    (Proj.basicOpenIsoSpec (grading K) (X i) (member K i) one_pos).inv ≫
      (Proj.basicOpen (grading K) (X i)).ι ≫ toBase K = _
  rw [← Category.assoc _ _ (toBase K),Proj.basicOpenIsoSpec_inv_ι,away_over,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (chartEval_constant K i)

lemma chart_smooth (i : Fin 2) : SmoothOfRelativeDimension 1
    ((Proj.basicOpen (grading K) (X i)).ι ≫ toBase K) := by
  have heq : (Proj.basicOpen (grading K) (X i)).ι ≫ toBase K =
      (chartSchemeIso K i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
    rw [← chart_over K i]; simp
  rw [heq]
  haveI := CurveModel.smoothOfRelativeDimension_one_Spec_polynomial K
  change SmoothOfRelativeDimension (0+1)
    ((chartSchemeIso K i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))))
  infer_instance

lemma charts_cover : (⨆ i : Fin 2, Proj.basicOpen (grading K) (X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (grading K) (X : Fin 2 → Ambient K)
    (ProjectiveQuotientCharts.irrelevant_le_span_X K 1)

lemma smooth : SmoothOfRelativeDimension 1 (toBase K) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun i : Fin 2 => Proj.basicOpen (grading K) (X i)) (charts_cover K)
  intro i
  exact chart_smooth K i

abbrev overlap := Away (grading K) (X (0:Fin 2)*X (1:Fin 2))
abbrev overlapRatio := Away.isLocalizationElem (member K 0) (member K 1)

def overlapMap : chart K 0 →+* overlap K := awayMap (grading K) (member K 1) rfl

lemma overlapRatio_image : chartEquiv K 0 (overlapRatio K) = Polynomial.X := by
  change chartEval K 0 (Away.mk (grading K) (member K 0) 1 ((X (1:Fin 2))^1) _) = _
  simp only [pow_one]
  rw [chartEval_mk]
  simp [evalChart]

lemma overlap_nontrivial : Nontrivial (overlap K) := by
  have hr : IsRegular (overlapRatio K) := by
    have hx : IsRegular (Polynomial.X : Polynomial K) := IsRegular.of_ne_zero Polynomial.X_ne_zero
    have he := overlapRatio_image K
    have hinj : Function.Injective (fun x : chart K 0 => overlapRatio K*x) := by
      intro x y hxy
      apply (chartEquiv K 0).injective
      apply hx.left
      change Polynomial.X * chartEquiv K 0 x = Polynomial.X * chartEquiv K 0 y
      rw [← he,← map_mul,← map_mul]
      exact congrArg (chartEquiv K 0) hxy
    exact ⟨hinj,fun x y hxy => hinj (by simpa only [mul_comm] using hxy)⟩
  letI := (overlapMap K).toAlgebra
  haveI : IsLocalization.Away (overlapRatio K) (overlap K) :=
    Away.isLocalization_mul (member K 0) (member K 1) rfl one_ne_zero
  have hi : Function.Injective (overlapMap K) := by
    change Function.Injective (algebraMap (chart K 0) (overlap K))
    apply IsLocalization.injectiveₛ (M := Submonoid.powers (overlapRatio K))
    rintro _ ⟨n,rfl⟩
    exact hr.pow n
  haveI : Nontrivial (chart K 0) := (chartEquiv K 0).toEquiv.nontrivial
  exact Function.Injective.nontrivial hi

lemma integral : IsIntegral (P1 K) := by
  let U : (P1 K).Opens := Proj.basicOpen (grading K) (X (0:Fin 2))
  let V : (P1 K).Opens := Proj.basicOpen (grading K) (X (1:Fin 2))
  haveI : IsIntegral U.toScheme := IsIntegral.of_isIso (chartSchemeIso K 0).inv
  haveI : IsIntegral V.toScheme := IsIntegral.of_isIso (chartSchemeIso K 1).inv
  have hc : U ⊔ V = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hx : x ∈ ⨆ i : Fin 2, Proj.basicOpen (grading K) (X i) := by rw [charts_cover]; trivial
    obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    change x ∈ U ∨ x ∈ V
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hne : ((U : Set (P1 K)) ∩ (V : Set (P1 K))).Nonempty := by
    letI := overlap_nontrivial K
    let x : Spec (.of (overlap K)) := Classical.choice inferInstance
    let y := Proj.awayι (grading K) (X (0:Fin 2)*X (1:Fin 2))
      (SetLike.mul_mem_graded (member K 0) (member K 1)) (by decide : 0 < 1+1) x
    have hy : y ∈ Proj.basicOpen (grading K) (X (0:Fin 2)*X (1:Fin 2)) := by
      rw [← Proj.opensRange_awayι (grading K) (X (0:Fin 2)*X (1:Fin 2))
        (SetLike.mul_mem_graded (member K 0) (member K 1)) (by decide : 0 < 1+1)]
      exact ⟨x,rfl⟩
    rw [Proj.basicOpen_mul] at hy
    exact ⟨y,hy.1,hy.2⟩
  exact integral_two_open U V hc hne

end FourCorner.ProjectiveLineCharts
#print axioms FourCorner.ProjectiveLineCharts.proper
#print axioms FourCorner.ProjectiveLineCharts.smooth
#print axioms FourCorner.ProjectiveLineCharts.integral
