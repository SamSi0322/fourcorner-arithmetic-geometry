import HpLiteralProjective

namespace FourCorner.HpNoTwoCoordinatesZero
open HasseRationalSource CompleteSource11
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem no_two_zero (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (x : Fin 5 → K) (he : Source p (x 0) (x 1) (x 2) (x 3) (x 4))
    (hn : ¬∀i,x i=0) : ∀i j,i ≠ j → x i=0 → x j=0 → False := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h4 : (4 : K) ≠ 0 := by norm_num
  have vanish (hz : x 0=0) (hu : x 1=0) : False := by
    have hv : x 2=0 := by
      have hh := he.1
      rw [hz,hu] at hh
      have hz' : p*(x 2)^2=0 := by simpa using hh
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz').resolve_left hp)
    have hw : x 3=0 := by
      have hh := he.2.1
      rw [hz,hu] at hh
      have hz' : p*(x 3)^2=0 := by simpa using hh
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz').resolve_left hp)
    have ht : x 4=0 := by
      have hh := he.2.2
      rw [hz,hu] at hh
      have hz' : p*(x 4)^2=0 := by simpa using hh
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz').resolve_left hp)
    apply hn
    intro i
    fin_cases i <;> assumption
  have h01 : ¬(x 0=0 ∧ x 1=0) := fun h => vanish h.1 h.2
  have h02 : ¬(x 0=0 ∧ x 2=0) := by
    rintro ⟨hz,hv⟩
    have hh := he.1
    rw [hz,hv] at hh
    have hU : 2*(p-1)*(x 1)^2=0 := by simpa using hh.symm
    exact vanish hz (sq_eq_zero_iff.mp ((mul_eq_zero.mp hU).resolve_left (mul_ne_zero h2 ha)))
  have h03 : ¬(x 0=0 ∧ x 3=0) := by
    rintro ⟨hz,hw⟩
    have hh := he.2.1
    rw [hz,hw] at hh
    have hU : 2*(p+1)*(x 1)^2=0 := by simpa using hh.symm
    exact vanish hz (sq_eq_zero_iff.mp ((mul_eq_zero.mp hU).resolve_left (mul_ne_zero h2 hb)))
  have h04 : ¬(x 0=0 ∧ x 4=0) := by
    rintro ⟨hz,ht⟩
    have hh := he.2.2
    rw [hz,ht] at hh
    have hU : (p-1)*(x 1)^2=0 := by simpa using hh.symm
    exact vanish hz (sq_eq_zero_iff.mp ((mul_eq_zero.mp hU).resolve_left ha))
  have h12 : ¬(x 1=0 ∧ x 2=0) := by
    rintro ⟨hu,hv⟩
    have hh := he.1
    rw [hu,hv] at hh
    have hz : (2*(p-1)*p)*(x 0)^2=0 := by linear_combination hh
    exact vanish (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero h2 ha) hp))) hu
  have h13 : ¬(x 1=0 ∧ x 3=0) := by
    rintro ⟨hu,hw⟩
    have hh := he.2.1
    rw [hu,hw] at hh
    have hz : (2*(p+1)*p)*(x 0)^2=0 := by linear_combination -hh
    exact vanish (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero h2 hb) hp))) hu
  have h14 : ¬(x 1=0 ∧ x 4=0) := by
    rintro ⟨hu,ht⟩
    have hh := he.2.2
    rw [hu,ht] at hh
    have hz : (p*(p+1))*(x 0)^2=0 := by linear_combination -hh
    exact vanish (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hp hb))) hu
  obtain ⟨hDU,hDW⟩ := omission_equations p (x 0) (x 1) (x 2) (x 3) (x 4) hp he
  have h23 : ¬(x 2=0 ∧ x 3=0) := by
    rintro ⟨hv,hw⟩
    have h0 := he.1
    have h1 := he.2.1
    rw [hv] at h0
    rw [hw] at h1
    have hz : (4*(p-1)*(p+1)*p)*(x 0)^2=0 := by
      linear_combination (p+1)*h0-(p-1)*h1
    have hz' : x 0=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 ha) hb) hp))
    exact h02 ⟨hz',hv⟩
  have h24 : ¬(x 2=0 ∧ x 4=0) := by
    rintro ⟨hv,ht⟩
    have hh := hDU.1
    rw [hv,ht] at hh
    have hz : (4*p)*(x 0)^2=0 := by linear_combination hh
    have hz' : x 0=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero h4 hp))
    exact h02 ⟨hz',hv⟩
  have h34 : ¬(x 3=0 ∧ x 4=0) := by
    rintro ⟨hw,ht⟩
    have hh := hDU.2
    rw [hw,ht] at hh
    have hz : (4*(p+1))*(x 0)^2=0 := by linear_combination hh
    have hz' : x 0=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero h4 hb))
    exact h03 ⟨hz',hw⟩
  intro i j hij hi hj
  fin_cases i <;> fin_cases j <;> simp_all

#print axioms no_two_zero
end
end FourCorner.HpNoTwoCoordinatesZero
