import FamilyConstituents
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Real.Cardinality
noncomputable section
open Filter Topology
namespace FourCorner

/-- A strict real source may be chosen with transcendental ell, so that it
gives an embedding of the actual Q(ell) function field into R. -/
theorem real_transcendental_source08 {t : ℝ} (ht : 1 < t)
    (htop : t < Real.sqrt 5 / 2) :
    ∃ S : CommonRootSource ℝ t, Transcendental ℚ S.ell ∧
      t-1 < S.ell ∧ S.ell < t+1 ∧ 0 < S.P ∧ 0 < S.B ∧
        |S.P*S.M| + |S.B*S.C| < 2 := by
  obtain ⟨S,hs,hT,hP,hB,hret⟩ := real_source_strict ht htop
  have he : 0 < S.ell := by linarith
  let f : ℝ → ℝ := fun x =>
    Real.sqrt (x+(t+1)) * Real.sqrt ((t-1)*((t+1)-x)/x) +
    Real.sqrt ((t+1)*(x+(t-1))/x) * Real.sqrt (x-(t-1))
  have hf : ContinuousAt f S.ell := by
    dsimp only [f]
    fun_prop (disch := exact S.ell_ne_zero)
  have hfe : f S.ell < 2 := by
    dsimp only [f]
    rw [← S.sqP,← S.sqM,← S.sqB,← S.sqC]
    simpa only [Real.sqrt_sq_eq_abs,← abs_mul] using hret
  have hnear : ∀ᶠ x in 𝓝 S.ell,
      t-1<x ∧ x<t+1 ∧ 0<x ∧ f x<2 :=
    (eventually_gt_nhds hs).and ((eventually_lt_nhds hT).and
      ((eventually_gt_nhds he).and (hf.eventually (eventually_lt_nhds hfe))))
  obtain ⟨a,b,⟨ha,hb⟩,hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  have hcount := Algebraic.countable ℚ ℝ
  have hex : ∃ e ∈ Set.Ioo a b, Transcendental ℚ e := by
    by_contra! hn
    have hc : (Set.Ioo a b).Countable := hcount.mono (by intro e he; exact not_not.mp (hn e he))
    exact (not_le_of_gt (ha.trans hb)) (Cardinal.Real.Ioo_countable_iff.1 hc)
  obtain ⟨e,heab,hetrans⟩ := hex
  obtain ⟨hse,heT,hepos,hfer⟩ := hab heab
  let P := Real.sqrt (e+(t+1))
  let C := Real.sqrt (e-(t-1))
  let M := Real.sqrt ((t-1)*((t+1)-e)/e)
  let B := Real.sqrt ((t+1)*(e+(t-1))/e)
  have hp : 0 < e+(t+1) := by linarith
  have hc : 0 < e-(t-1) := by linarith
  have hm : 0 < (t-1)*((t+1)-e)/e :=
    div_pos (mul_pos (by linarith) (by linarith)) hepos
  have hb : 0 < (t+1)*(e+(t-1))/e :=
    div_pos (mul_pos (by linarith) (by linarith)) hepos
  have pp : 0 < P := Real.sqrt_pos.mpr hp
  have cp : 0 < C := Real.sqrt_pos.mpr hc
  have mp : 0 < M := Real.sqrt_pos.mpr hm
  have bp : 0 < B := Real.sqrt_pos.mpr hb
  let S' : CommonRootSource ℝ t := {
    ell := e, P := P, C := C, M := M, B := B
    t_ne_zero := by linarith
    t_ne_one := ne_of_gt ht
    t_ne_neg_one := by linarith
    ell_ne_zero := ne_of_gt hepos
    P_ne_zero := ne_of_gt pp
    C_ne_zero := ne_of_gt cp
    M_ne_zero := ne_of_gt mp
    B_ne_zero := ne_of_gt bp
    sqP := Real.sq_sqrt hp.le
    sqC := Real.sq_sqrt hc.le
    sqM := Real.sq_sqrt hm.le
    sqB := Real.sq_sqrt hb.le }
  refine ⟨S',hetrans,hse,heT,pp,bp,?_⟩
  change |P*M|+|B*C|<2
  rw [abs_of_pos (mul_pos pp mp),abs_of_pos (mul_pos bp cp)]
  exact hfer
#print axioms real_transcendental_source08
end FourCorner
