import HpStrictRealPoint
import HpModelFieldPoint
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Real.Cardinality

namespace FourCorner.HpStrictRealGeneric
open HasseNorms HpStrictRealPoint Filter Topology AlgebraicGeometry CategoryTheory
noncomputable section

/-- A Q-transcendental parameter lies in the literal strict real distance
region, so that the SAME solution induces an actual model point. -/
theorem strict_real_transcendental (p : ℝ) (hp : 1<p) :
    ∃S : LocalPoint ℝ p,Transcendental ℚ S.rho ∧ 1<S.rho ∧
      0<2*S.t^2-4*|S.u|-|S.v*S.w| := by
  obtain ⟨S,hS,hmargin⟩ := strict_real_point p hp
  have hm : 0<margin p S.rho := by
    have hu : |S.u|=Real.sqrt (p*S.rho) := by rw [← S.sqU,Real.sqrt_sq_eq_abs]
    have hv : |S.v|=Real.sqrt (2*(p-1)*(S.rho-1)) := by rw [← S.sqV,Real.sqrt_sq_eq_abs]
    have hw : |S.w|=Real.sqrt (2*(p+1)*(S.rho+1)) := by rw [← S.sqW,Real.sqrt_sq_eq_abs]
    dsimp [margin]
    rw [← S.sqT,← hu,← hv,← hw,← abs_mul]
    exact hmargin
  have hnear : ∀ᶠx in 𝓝 S.rho,1<x ∧ 0<margin p x :=
    (eventually_gt_nhds hS).and ((margin_continuous p).continuousAt.eventually
      (eventually_gt_nhds hm))
  obtain ⟨a,b,⟨ha,hb⟩,hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  have hcount := Algebraic.countable ℚ ℝ
  have hex : ∃rho∈Set.Ioo a b,Transcendental ℚ rho := by
    by_contra! hn
    have hc : (Set.Ioo a b).Countable := hcount.mono (by intro e he;exact not_not.mp (hn e he))
    exact (not_le_of_gt (ha.trans hb)) (Cardinal.Real.Ioo_countable_iff.1 hc)
  obtain ⟨rho,hrab,htrans⟩ := hex
  obtain ⟨hrho,hm⟩ := hab hrab
  have hU : 0<p*rho := mul_pos (by linarith) (by linarith)
  have hV : 0<2*(p-1)*(rho-1) := by positivity
  have hW : 0<2*(p+1)*(rho+1) := by positivity
  have hT : 0<(p-1)*rho+p+1 := by positivity
  let u := Real.sqrt (p*rho)
  let v := Real.sqrt (2*(p-1)*(rho-1))
  let w := Real.sqrt (2*(p+1)*(rho+1))
  let t := Real.sqrt ((p-1)*rho+p+1)
  have hu : 0<u := Real.sqrt_pos.mpr hU
  have hv : 0<v := Real.sqrt_pos.mpr hV
  have hw : 0<w := Real.sqrt_pos.mpr hW
  have ht : 0<t := Real.sqrt_pos.mpr hT
  have hu2 : u^2=p*rho := Real.sq_sqrt hU.le
  have hv2 : v^2=2*(p-1)*(rho-1) := Real.sq_sqrt hV.le
  have hw2 : w^2=2*(p+1)*(rho+1) := Real.sq_sqrt hW.le
  have ht2 : t^2=(p-1)*rho+p+1 := Real.sq_sqrt hT.le
  let S : LocalPoint ℝ p := ⟨rho,u,v,w,t,by linarith,by linarith,by linarith,
    ne_of_gt hu,ne_of_gt hv,ne_of_gt hw,ne_of_gt ht,hu2,hv2,hw2,ht2⟩
  refine ⟨S,htrans,hrho,?_⟩
  change 0<2*t^2-4*|u|-|v*w|
  rw [ht2,abs_of_pos hu,abs_of_pos (mul_pos hv hw)]
  exact hm

theorem family_strict_real_transcendental (j : ℕ) :
    ∃S : LocalPoint ℝ (HpInfiniteArithmetic.p j : ℝ),Transcendental ℚ S.rho ∧ 1<S.rho ∧
      0<2*S.t^2-4*|S.u|-|S.v*S.w| :=
  strict_real_transcendental _ (by exact_mod_cast HpInfiniteArithmetic.p_gt_one j)

/-- Actual real point of the SAME smooth proper model, from the proved
strict real source and an actual function-field embedding. -/
theorem family_model_real_point (j : ℕ) :
    ∃f : Spec (CommRingCat.of ℝ) ⟶ HpSchemeModel.curve (HpInfiniteArithmetic.p j),
      f ≫ HpSchemeModel.toBase (HpInfiniteArithmetic.p j)=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) := by
  obtain ⟨S,htrans,hstrict,hm⟩ := family_strict_real_transcendental j
  let r : Fin 4 → ℝ := ![S.u,S.v,S.w,S.t]
  have hr (i : Fin 4) : r i^2=HpResidueCharts.values (HpInfiniteArithmetic.p j : ℝ) S.rho i := by
    fin_cases i
    · exact S.sqU
    · exact S.sqV
    · exact S.sqW
    · exact S.sqT
  exact ⟨HpModelFieldPoint.point _ (HpInfiniteArithmetic.p_gt_one j) S.rho htrans r hr,
    HpModelFieldPoint.point_overQ _ (HpInfiniteArithmetic.p_gt_one j) S.rho htrans r hr⟩

#print axioms strict_real_transcendental
#print axioms family_model_real_point
end
end FourCorner.HpStrictRealGeneric
