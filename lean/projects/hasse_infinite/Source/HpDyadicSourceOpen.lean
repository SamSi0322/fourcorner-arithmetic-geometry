import HpStrictRealGeneric
import HpOddSourceOpen

namespace FourCorner.HpDyadicSourceOpen
open HasseNorms HpResidueCharts HpHenselOrdinary Filter Topology
noncomputable section
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A literal dyadic principal-unit neighbourhood, obtained from the
proved all-depth 1+8Z₂ square theorem, including the exact center. -/
theorem roots_near_one (x : ℚ_[2]) (hx : ‖x-1‖<(2 : ℝ)^(-2 : ℤ)) :
    ∃z : ℚ_[2],z ≠ 0 ∧ z^2=x := by
  by_cases he : x=1
  · exact ⟨1,one_ne_zero,by rw [he];norm_num⟩
  have hd : x-1 ≠ 0 := sub_ne_zero.mpr he
  have hv : 3≤(x-1).valuation := by
    rw [Padic.norm_eq_zpow_neg_valuation hd] at hx
    have hh := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mp hx
    omega
  exact HpDyadicFamilyPoint.principal_square_root x hv

/-- Every strict original Q₂ point has a nearby Q-transcendental source
point. Every radicand is normalized by its actual initial nonzero square. -/
theorem transcendental_source (p : ℚ) (S : LocalPoint ℚ_[2] (p : ℚ_[2])) :
    ∃S' : LocalPoint ℚ_[2] (p : ℚ_[2]),Transcendental ℚ S'.rho := by
  let R : Fin 4 → ℚ_[2] := ![S.u,S.v,S.w,S.t]
  have hR (i : Fin 4) : R i ≠ 0 := by
    fin_cases i
    · exact S.u_ne_zero
    · exact S.v_ne_zero
    · exact S.w_ne_zero
    · exact S.t_ne_zero
  have hRs (i : Fin 4) : R i^2=values (p : ℚ_[2]) S.rho i := by
    fin_cases i
    · exact S.sqU
    · exact S.sqV
    · exact S.sqW
    · exact S.sqT
  let f (i : Fin 4) (e : ℚ_[2]) := values (p : ℚ_[2]) e i/(R i)^2
  have hfe (i : Fin 4) : f i S.rho=1 := by dsimp [f];rw [← hRs];exact div_self (pow_ne_zero _ (hR i))
  have hnear (i : Fin 4) : ∀ᶠe in 𝓝 S.rho,‖f i e-1‖<(2 : ℝ)^(-2 : ℤ) := by
    have hc : ContinuousAt (fun e => ‖f i e-1‖) S.rho := by
      dsimp [f]
      exact (((continuous_values _ i).continuousAt.div_const _).sub continuousAt_const).norm
    have hh : ‖f i S.rho-1‖<(2 : ℝ)^(-2 : ℤ) := by rw [hfe,sub_self,norm_zero];positivity
    exact hc.eventually (eventually_lt_nhds hh)
  have hAll : ∀ᶠe in 𝓝 S.rho,∀i : Fin 4,‖f i e-1‖<(2 : ℝ)^(-2 : ℤ) := Filter.eventually_all.mpr hnear
  obtain ⟨U,hsub,hU,hc⟩ := mem_nhds_iff.mp hAll
  obtain ⟨e,heU,he⟩ := PadicTranscendental.exists_in_open hU ⟨S.rho,hc⟩
  have hr (i : Fin 4) : ∃z : ℚ_[2],z ≠ 0 ∧ z^2=f i e := roots_near_one _ (hsub heU i)
  choose z hz hs using hr
  let r (i : Fin 4) := R i*z i
  have hr0 (i : Fin 4) : r i ≠ 0 := mul_ne_zero (hR i) (hz i)
  have hrs (i : Fin 4) : r i^2=values (p : ℚ_[2]) e i := by
    dsimp [r]
    rw [mul_pow,hs]
    dsimp [f]
    field_simp [hR i]
  exact ⟨toLocalPoint p e he r hr0 hrs,he⟩

#print axioms roots_near_one
#print axioms transcendental_source
end
end FourCorner.HpDyadicSourceOpen
