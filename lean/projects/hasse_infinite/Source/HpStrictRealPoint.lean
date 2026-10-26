import HpFamilyNoPoint
import Mathlib.Analysis.Real.Sqrt

namespace FourCorner.HpStrictRealPoint

open HasseNorms

noncomputable def margin (p rho : ℝ) : ℝ :=
  2*((p-1)*rho+p+1)-4*Real.sqrt (p*rho)-
    Real.sqrt (2*(p-1)*(rho-1))*Real.sqrt (2*(p+1)*(rho+1))

theorem margin_continuous (p : ℝ) : Continuous (margin p) := by
  unfold margin
  fun_prop

theorem margin_at_one_positive (p : ℝ) (hp : 1<p) : 0<margin p 1 := by
  have hs : Real.sqrt p<p := Real.sqrt_lt_self_iff.mpr hp
  have he : margin p 1=4*p-4*Real.sqrt p := by simp [margin];ring
  rw [he]
  linarith

/-- The actual ordered four-square source has a point in the paper's strict
real distance region, with the literal strict margin positive. -/
theorem strict_real_point (p : ℝ) (hp : 1<p) :
    ∃ S : LocalPoint ℝ p, 1<S.rho ∧
      0<2*S.t^2-4*|S.u|-|S.v*S.w| := by
  have hpos := (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 1).eventually_lt
    (margin_continuous p).continuousAt (margin_at_one_positive p hp)
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp hpos
  let rho : ℝ := 1+eps/2
  have hrho : 1<rho := by dsimp [rho];linarith
  have hmem : rho∈Metric.ball (1 : ℝ) eps := by
    change dist rho 1<eps
    rw [Real.dist_eq]
    dsimp [rho]
    have he : 1+eps/2-1=eps/2 := by ring
    rw [he,abs_of_pos (by linarith : 0<eps/2)]
    linarith
  have hm : 0<margin p rho := hball hmem
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
  refine ⟨S,hrho,?_⟩
  change 0<2*t^2-4*|u|-|v*w|
  rw [ht2,abs_of_pos hu,abs_of_pos (mul_pos hv hw)]
  exact hm

theorem family_strict_real_point (j : ℕ) :
    ∃ S : LocalPoint ℝ (HpInfiniteArithmetic.p j : ℝ), 1<S.rho ∧
      0<2*S.t^2-4*|S.u|-|S.v*S.w| := by
  apply strict_real_point
  exact_mod_cast HpInfiniteArithmetic.p_gt_one j

#print axioms strict_real_point
#print axioms family_strict_real_point

end FourCorner.HpStrictRealPoint
