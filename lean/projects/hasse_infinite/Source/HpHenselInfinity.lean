import HpHenselOrdinary

namespace FourCorner.HpHenselInfinity
open HpResidueCharts HpHenselOrdinary PadicUnitNeighbourhood
noncomputable section
variable {q : ℕ} [Fact q.Prime]

theorem continuous_infinityValues (p pinv : ℚ_[q]) (i : Fin 3) :
    Continuous (fun e : ℚ_[q] => infinityValues p pinv e i) := by
  fin_cases i <;> simp only [infinityValues] <;> fun_prop

/-- Every actual rational point above infinity lifts at a Q-transcendental
parameter by the original normalized-root chart. -/
theorem infinity (hq : q ≠ 2) (p : ℚ) (hp : p ≠ 0) (P PI : ℤ_[q])
    (hP : (P : ℚ_[q])=(p : ℚ_[q])) (hPI : (PI : ℚ_[q])=(p : ℚ_[q])⁻¹)
    (r0 : Fin 3 → ZMod q)
    (hr0 : ∀i,r0 i^2=infinityValues (PadicInt.toZMod P) (PadicInt.toZMod PI) 0 i)
    (hn : ∀i,r0 i ≠ 0) :
    ∃S : HasseNorms.LocalPoint ℚ_[q] (p : ℚ_[q]),Transcendental ℚ S.rho := by
  let f (i : Fin 3) (u : ℚ_[q]) := infinityValues (p : ℚ_[q]) (p : ℚ_[q])⁻¹ ((p : ℚ_[q])*u^2) i
  let v (i : Fin 3) := infinityValues P PI 0 i
  have ha (i : Fin 3) : PadicInt.toZMod (v i)=r0 i^2 := by
    have hh := map_infinityValues PadicInt.toZMod P PI 0 i
    rw [map_zero] at hh
    exact hh.trans (hr0 i).symm
  obtain ⟨u,hu,hr⟩ := transcendental_simultaneous_roots hq f 0 v
    (fun i => (continuous_infinityValues _ _ i).continuousAt.comp
      (by fun_prop : ContinuousAt (fun u : ℚ_[q] => (p : ℚ_[q])*u^2) 0))
    (fun i => by
      have hTwo : ((2 : ℤ_[q]) : ℚ_[q])=(2 : ℚ_[q]) := rfl
      fin_cases i <;> simp only [f,v,infinityValues,zero_pow (by decide : 2 ≠ 0),
        mul_zero,sub_zero,add_zero,PadicInt.coe_mul,PadicInt.coe_add,PadicInt.coe_sub,
        PadicInt.coe_one,PadicInt.coe_zero,hTwo,hP,hPI])
    (fun i => by rw [ha];exact pow_ne_zero _ (hn i))
    (fun i => by rw [ha];exact IsSquare.sq _)
  choose z hz hs using hr
  have hu0 : u ≠ 0 := by intro he;apply hu;rw [he];exact isAlgebraic_zero
  have hp0 : (p : ℚ_[q]) ≠ 0 := by exact_mod_cast hp
  let e : ℚ_[q] := ((p⁻¹ : ℚ) : ℚ_[q])/u^2
  have he : Transcendental ℚ e := TranscendentalParameters.inverse_square hu p⁻¹ (inv_ne_zero hp)
  let r : Fin 4 → ℚ_[q] := ![1/u,z 0/u,z 1/u,z 2/u]
  have hrne (i : Fin 4) : r i ≠ 0 := by
    fin_cases i
    · exact div_ne_zero one_ne_zero hu0
    · exact div_ne_zero (hz 0) hu0
    · exact div_ne_zero (hz 1) hu0
    · exact div_ne_zero (hz 2) hu0
  have hrs (i : Fin 4) : r i^2=values (p : ℚ_[q]) e i := by
    have h0 := hs 0
    have h1 := hs 1
    have h2 := hs 2
    change (z 0)^2=2*((p : ℚ_[q])-1)*(p : ℚ_[q])⁻¹*(1-(p : ℚ_[q])*u^2) at h0
    change (z 1)^2=2*((p : ℚ_[q])+1)*(p : ℚ_[q])⁻¹*(1+(p : ℚ_[q])*u^2) at h1
    change (z 2)^2=((p : ℚ_[q])-1)*(p : ℚ_[q])⁻¹+((p : ℚ_[q])+1)*(p : ℚ_[q])⁻¹*((p : ℚ_[q])*u^2) at h2
    fin_cases i
    · change (1/u)^2=(p : ℚ_[q])*e
      dsimp [e]
      push_cast
      field_simp [hu0,hp0]
    · change (z 0/u)^2=2*((p : ℚ_[q])-1)*(e-1)
      rw [div_pow,h0]
      dsimp [e]
      push_cast
      field_simp [hu0,hp0]
      <;> ring
    · change (z 1/u)^2=2*((p : ℚ_[q])+1)*(e+1)
      rw [div_pow,h1]
      dsimp [e]
      push_cast
      field_simp [hu0,hp0]
      <;> ring
    · change (z 2/u)^2=((p : ℚ_[q])-1)*e+(p : ℚ_[q])+1
      rw [div_pow,h2]
      dsimp [e]
      push_cast
      field_simp [hu0,hp0]
      <;> ring
  exact ⟨toLocalPoint p e he r hrne hrs,he⟩

#print axioms infinity
end
end FourCorner.HpHenselInfinity
