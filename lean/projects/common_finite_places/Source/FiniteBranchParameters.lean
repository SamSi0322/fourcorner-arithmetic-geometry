import FiniteHenselRealization

noncomputable section
namespace FourCorner.FiniteBranchParameters

def center {R : Type*} [CommRing R] (t : R) : Fin 5 → R
  | 0 => -(t+1)
  | 1 => t-1
  | 2 => t+1
  | 3 => -(t-1)
  | 4 => 0

def slope {R : Type*} [Field R] (t κ : R) : Fin 5 → R
  | 0 => 1
  | 1 => 1
  | 2 => -κ/(t-1)
  | 3 => κ/(t+1)
  | 4 => κ

theorem slope_nonzero {R : Type*} [Field R] (t κ : R)
    (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) (i : Fin 5) : slope t κ i ≠ 0 := by
  have hs : t-1 ≠ 0 := sub_ne_zero.mpr h1
  have hT : t+1 ≠ 0 := by intro h; exact hm (eq_neg_of_add_eq_zero_left h)
  fin_cases i <;> simp [slope,hκ,hs,hT]

theorem pivot_equation {R : Type*} [Field R] (t κ : R)
    (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) (i : Fin 5) (u : R) :
    u^2 = RadicalLinearization.values t κ⁻¹ (center t i+slope t κ i*u^2) i := by
  have hs : t-1 ≠ 0 := sub_ne_zero.mpr h1
  have hT : t+1 ≠ 0 := by intro h; exact hm (eq_neg_of_add_eq_zero_left h)
  fin_cases i <;> simp only [center,slope,RadicalLinearization.values]
  all_goals field_simp [hs,hT,hκ] <;> ring

theorem center_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (i : Fin 5) : f (center t i) = center (f t) i := by
  fin_cases i <;> simp only [center,map_neg,map_add,map_sub,map_one,map_zero]

theorem slope_map {R S : Type*} [Field R] [Field S]
    (f : R →+* S) (t κ : R) (i : Fin 5) : f (slope t κ i) = slope (f t) (f κ) i := by
  fin_cases i <;> simp only [slope,map_neg,map_div₀,map_sub,map_add,map_one]

end FourCorner.FiniteBranchParameters
#print axioms FourCorner.FiniteBranchParameters.pivot_equation
#print axioms FourCorner.FiniteBranchParameters.slope_nonzero
