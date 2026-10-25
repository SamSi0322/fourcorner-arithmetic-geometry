import FourCorner.CommonRootRamifiedNecessity

set_option autoImplicit false
namespace FourCorner.CommonRootSource

/-- If `t+1` is a nonsquare unit, every actual source coordinate has norm
one. The proof treats arbitrary positive and negative valuation depths. -/
theorem ell_norm_one_of_nonsquare_T {p : ℕ} [Fact p.Prime] {t : ℚ_[p]}
    (S : CommonRootSource ℚ_[p] t) (hp : p ≠ 2)
    (ht : ‖t‖ ≤ 1) (hT : ‖t+1‖ = 1) (hns : ¬ IsSquare (t+1)) :
    ‖S.ell‖ = 1 := by
  have hT0 : t+1 ≠ 0 := by intro hz; simp [hz] at hT
  have hs : ‖t-1‖ ≤ 1 := by
    calc
      ‖t-1‖ ≤ max ‖t‖ ‖(-1 : ℚ_[p])‖ := by simpa only [sub_eq_add_neg] using Padic.nonarchimedean t (-1)
      _ ≤ 1 := max_le ht (by simp)
  rcases lt_trichotomy ‖S.ell‖ 1 with he | he | he
  · exfalso
    apply hns
    apply (padic_odd_isSquare_iff_of_norm_sub_lt hp hT0 (y:=S.P^2) ?_).mpr
      (IsSquare.sq S.P)
    rw [S.sqP,add_sub_cancel_right,hT]
    exact he
  · exact he
  · exfalso
    apply hns
    apply (padic_odd_isSquare_iff_of_norm_sub_lt hp hT0 (y:=S.B^2) ?_).mpr
      (IsSquare.sq S.B)
    have hid : S.B^2-(t+1)=(t+1)*(t-1)/S.ell := by
      rw [S.sqB]
      field_simp [S.ell_ne_zero]
      ring
    rw [hid,norm_div,norm_mul,hT,one_mul]
    exact (div_lt_one (lt_trans zero_lt_one he)).mpr (lt_of_le_of_lt hs he)

end FourCorner.CommonRootSource
#print axioms FourCorner.CommonRootSource.ell_norm_one_of_nonsquare_T
