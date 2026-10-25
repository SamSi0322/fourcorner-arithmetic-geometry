import FourCorner.NineSmallASignedSupport
import FourCorner.NineSmallALocal

namespace FourCorner.NineSmallA

/-- A non-root rational point on the first auxiliary curve has positive
abscissa. -/
lemma abscissa_pos {x y : ℚ} (hy : y ≠ 0)
    (h : y^2=x*(x-6)*(x-8)) : 0 < x := by
  by_contra hx
  have hx0 : x ≤ 0 := le_of_not_gt hx
  have hp : 0 ≤ x*(x-6) := mul_nonneg_of_nonpos_of_nonpos hx0 (by linarith)
  have hn : x*(x-6)*(x-8) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp (by linarith)
  nlinarith [sq_pos_of_ne_zero hy]

/-- Every ordinary point has one of four ordered square-class rows. The
three roots belong to the same point; they are not independently chosen
local labels. -/
theorem ordinary_coordinate_rows {x y : ℚ} (hy : y ≠ 0)
    (h : y^2=x*(x-6)*(x-8)) :
    ∃ a c : ℤ, ((a=1 ∧ c=1) ∨ (a=2 ∧ c=1) ∨
      (a=3 ∧ c= -2) ∨ (a=6 ∧ c= -2)) ∧
      ∃ u v z : ℚ, u ≠ 0 ∧ v ≠ 0 ∧ z ≠ 0 ∧
        x=(a:ℚ)*u^2 ∧ x-6=((a*c:ℤ):ℚ)*v^2 ∧ x-8=(c:ℚ)*z^2 := by
  have hx := abscissa_pos hy h
  have hx8 : x-8 ≠ 0 := by
    intro heq
    have : x=8 := by linarith
    rw [this] at h
    norm_num at h
    exact hy h
  obtain ⟨n, hn, u, hu, hxu⟩ := FourCorner.smallA_first_slot hx h
  obtain ⟨c, hc, z, hz, hxz⟩ := FourCorner.smallA_eight_slot hx8 h
  have ha : (n:ℤ)=1 ∨ (n:ℤ)=2 ∨ (n:ℤ)=3 ∨ (n:ℤ)=6 := by
    rcases hn with rfl|rfl|rfl|rfl <;> norm_num
  have hc' : c=1 ∨ c=2 ∨ c= -1 ∨ c= -2 := by tauto
  have hnq : (n:ℚ) ≠ 0 := by rcases hn with rfl|rfl|rfl|rfl <;> norm_num
  have hcq : (c:ℚ) ≠ 0 := by rcases hc with rfl|rfl|rfl|rfl <;> norm_num
  let v : ℚ := y/((n:ℚ)*c*u*z)
  have hv : v ≠ 0 := div_ne_zero hy (mul_ne_zero (mul_ne_zero (mul_ne_zero hnq hcq) hu.ne') hz.ne')
  have hmid : x-6=((n:ℤ)*c:ℤ)*v^2 := by
    push_cast
    symm
    calc
      (n:ℚ)*c*v^2 = y^2/((n:ℚ)*c*u^2*z^2) := by
        dsimp [v]
        field_simp
        <;> ring
      _ = ((n:ℚ)*u^2)*(x-6)*((c:ℚ)*z^2)/((n:ℚ)*c*u^2*z^2) := by
        rw [h, hxz, hxu]
      _ = x-6 := by field_simp
  have h1 : ((n:ℤ):ℚ)*u^2-(((n:ℤ)*c:ℤ):ℚ)*v^2=6 := by
    rw [←hmid]
    norm_cast
    linarith [hxu]
  have h2 : ((n:ℤ):ℚ)*u^2-(c:ℚ)*z^2=8 := by
    norm_cast
    linarith [hxu,hxz]
  exact ⟨n,c,rational_row_classification _ _ _ _ _ ha hc' h1 h2,
    u,v,z,hu.ne',hv,hz.ne',by exact_mod_cast hxu,hmid,hxz⟩

end FourCorner.NineSmallA
#print axioms FourCorner.NineSmallA.ordinary_coordinate_rows
