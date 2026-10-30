import HpGoodFiniteLift

namespace FourCorner.HpGoodLocal
open HpResidueCharts HpGoodFiniteLift
noncomputable section
variable {q : ℕ} [Fact q.Prime]

theorem residue_two_ne_zero (hq : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro he
  have hd := (ZMod.natCast_eq_zero_iff 2 q).mp he
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (Fact.out : q.Prime).ne_one h
  · exact hq h

/-- Both exhaustive residue charts give actual Qq points at parameters
with original good reduction; all infinity roots are proved to be units. -/
theorem charts_lift (hq : q ≠ 2) (p : ℚ) (hp : 1<p) (P : ℤ_[q])
    (hP : (P : ℚ_[q])=(p : ℚ_[q]))
    (hP0 : PadicInt.toZMod P ≠ 0) (hPa : PadicInt.toZMod P-1 ≠ 0)
    (hPb : PadicInt.toZMod P+1 ≠ 0)
    (hchart : (∃a : ZMod q,∃r : Fin 4 → ZMod q,∀i,r i^2=values (PadicInt.toZMod P) a i) ∨
      (∃r : Fin 3 → ZMod q,∀i,r i^2=infinityValues (PadicInt.toZMod P) (PadicInt.toZMod P)⁻¹ 0 i)) :
    ∃S : HasseNorms.LocalPoint ℚ_[q] (p : ℚ_[q]),Transcendental ℚ S.rho := by
  rcases hchart with ⟨a,r,hr⟩ | ⟨r,hr⟩
  · exact HpGoodFiniteLift.finite hq p hp P hP hP0 hPa hPb a r hr
  · have hnorm := norm_eq_one_of_residue P hP0
    let PI : ℤ_[q] := ⟨(P : ℚ_[q])⁻¹,by rw [norm_inv,hnorm];norm_num⟩
    have hPI : (PI : ℚ_[q])=(p : ℚ_[q])⁻¹ := by change (P : ℚ_[q])⁻¹=_;rw [hP]
    have hPPI : P*PI=1 := by
      apply Subtype.ext
      change (P : ℚ_[q])*(P : ℚ_[q])⁻¹=1
      exact mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hnorm];norm_num))
    have hPIres : PadicInt.toZMod PI=(PadicInt.toZMod P)⁻¹ := by
      have hh := congrArg PadicInt.toZMod hPPI
      rw [map_mul,map_one] at hh
      apply mul_left_cancel₀ hP0
      rw [mul_inv_cancel₀ hP0]
      exact hh
    have hn (i : Fin 3) : r i ≠ 0 := by
      intro hz
      have hh := hr i
      rw [hz,zero_pow (by decide : 2 ≠ 0)] at hh
      have h2 := residue_two_ne_zero hq
      have hpinv : (PadicInt.toZMod P)⁻¹ ≠ 0 := inv_ne_zero hP0
      fin_cases i <;> simp only [infinityValues,mul_zero,add_zero,sub_zero,mul_one] at hh
      · exact (mul_ne_zero (mul_ne_zero h2 hPa) hpinv) hh.symm
      · exact (mul_ne_zero (mul_ne_zero h2 hPb) hpinv) hh.symm
      · exact (mul_ne_zero hPa hpinv) hh.symm
    apply HpHenselInfinity.infinity hq p (by linarith) P PI hP hPI r
    · simpa only [hPIres] using hr
    · exact hn

/-- The actual genus-five finite-field curve has a rational place for
every q≥101. Its SAME-place exhaustive charts lift to the original source. -/
theorem large_good_prime (hq : q ≠ 2) (hlarge : 101≤q) (p : ℚ) (hp : 1<p) (P : ℤ_[q])
    (hP : (P : ℚ_[q])=(p : ℚ_[q]))
    (hP0 : PadicInt.toZMod P ≠ 0) (hPa : PadicInt.toZMod P-1 ≠ 0)
    (hPb : PadicInt.toZMod P+1 ≠ 0) :
    ∃S : HasseNorms.LocalPoint ℚ_[q] (p : ℚ_[q]),Transcendental ℚ S.rho := by
  letI : NeZero (2 : ZMod q) := ⟨residue_two_ne_zero hq⟩
  obtain ⟨w,hw⟩ := HpFiniteBaseGenus.exists_rational_place (ZMod q) (PadicInt.toZMod P) hP0 hPa hPb
    (by simpa only [Nat.card_eq_fintype_card,ZMod.card] using hlarge)
  exact charts_lift hq p hp P hP hP0 hPa hPb
    (HpResidueCharts.exhaustive_charts (ZMod q) (PadicInt.toZMod P) hP0 w hw)

#print axioms charts_lift
#print axioms large_good_prime
end
end FourCorner.HpGoodLocal
