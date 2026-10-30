import ThetaCoverClassPortable.FourCorner.ThetaBitangentCore

namespace FourCorner

variable {K : Type*} [Field K] [CharZero K]

theorem theta_contact_I_half (u x y : K) (hu : u^2=1/2) :
    thetaF x y (u*x) = 9801*(y^2-x^2/99)^2 := by
  have hu4 : u^4=(1/2:K)^2 := by calc
    _ = (u^2)^2 := by ring
    _ = _ := by rw [hu]
  simp only [thetaF,mul_pow,hu,hu4]
  ring

theorem theta_contact_I_fifty (u x y : K) (hu : u^2=50) :
    thetaF x y (u*x) = 9801*(y^2-9899*x^2/99)^2 := by
  have hu4 : u^4=(50:K)^2 := by calc
    _ = (u^2)^2 := by ring
    _ = _ := by rw [hu]
  simp only [thetaF,mul_pow,hu,hu4]
  ring

theorem thetaF_swap (x y z : K) : thetaF x y z = thetaF y x z := by
  unfold thetaF
  ring

theorem theta_contact_I_half_swap (u x y : K) (hu : u^2=1/2) :
    thetaF x y (u*y) = 9801*(x^2-y^2/99)^2 := by
  rw [thetaF_swap]
  exact theta_contact_I_half u y x hu

theorem theta_contact_I_fifty_swap (u x y : K) (hu : u^2=50) :
    thetaF x y (u*y) = 9801*(x^2-9899*y^2/99)^2 := by
  rw [thetaF_swap]
  exact theta_contact_I_fifty u y x hu

theorem theta_contact_II_nine (ε η x y : K) (he : ε^2=1) (hh : η^2=1) :
    thetaF x y (9*(ε*x+η*y)/14) =
      (13122/49:K)*(x^2+ε*η*(-818/81)*x*y+y^2)^2 := by
  rcases sq_eq_one_iff.mp he with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hh with rfl | rfl <;> unfold thetaF <;> ring

theorem theta_contact_II_eleven (ε η x y : K) (he : ε^2=1) (hh : η^2=1) :
    thetaF x y (11*(ε*x+η*y)/14) =
      (29282/49:K)*(x^2+ε*η*(1222/121)*x*y+y^2)^2 := by
  rcases sq_eq_one_iff.mp he with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hh with rfl | rfl <;> unfold thetaF <;> ring

theorem theta_contact_III_nine_eleven (s ε η x y : K)
    (hs : s^2=51) (he : ε^2=1) (hh : η^2=1) :
    thetaF x y (s*(ε*9*x+η*11*y)/102) =
      (6534/17:K)*(x^2+ε*η*(-980/99)*x*y-y^2)^2 := by
  have hs4 : s^4=(51:K)^2 := by calc
    _ = (s^2)^2 := by ring
    _ = _ := by rw [hs]
  rcases sq_eq_one_iff.mp he with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hh with rfl | rfl <;>
    simp only [thetaF,div_pow,mul_pow,hs,hs4] <;> ring

theorem theta_contact_III_eleven_nine (s ε η x y : K)
    (hs : s^2=51) (he : ε^2=1) (hh : η^2=1) :
    thetaF x y (s*(ε*11*x+η*9*y)/102) =
      (6534/17:K)*(x^2+ε*η*(980/99)*x*y-y^2)^2 := by
  have hs4 : s^4=(51:K)^2 := by calc
    _ = (s^2)^2 := by ring
    _ = _ := by rw [hs]
  rcases sq_eq_one_iff.mp he with rfl | rfl <;>
    rcases sq_eq_one_iff.mp hh with rfl | rfl <;>
    simp only [thetaF,div_pow,mul_pow,hs,hs4] <;> ring

theorem theta_vertical_quartic_relation (t s η : K)
    (hs : s^2=51) (hh : η^2=1) (ht : t^2=50+7*η*s) :
    t^4-100*t^2+1=0 := by
  linear_combination (t^2-50+7*η*s)*ht + 49*η^2*hs + 2499*hh

theorem theta_contact_IV_of_quartic (t y z : K) (ht : t^4-100*t^2+1=0) :
    thetaF (t*y) y z =
      39984*(z^2-39592*(t^2+1)/79968*y^2)^2 := by
  unfold thetaF
  linear_combination (2/51:K)*y^4*ht

theorem theta_contact_IV (t s η y z : K)
    (hs : s^2=51) (hh : η^2=1) (ht : t^2=50+7*η*s) :
    thetaF (t*y) y z =
      39984*(z^2-39592*(t^2+1)/79968*y^2)^2 :=
  theta_contact_IV_of_quartic t y z (theta_vertical_quartic_relation t s η hs hh ht)

theorem theta_vertical_t_sq_add_one_ne_zero (t : K) (ht : t^4-100*t^2+1=0) :
    t^2+1≠0 := by
  intro h
  have ht2 : t^2=(-1:K) := add_eq_zero_iff_eq_neg.mp h
  have ht4 : t^4=(1:K) := by calc
    _ = (t^2)^2 := by ring
    _ = _ := by rw [ht2]; ring
  norm_num [ht2,ht4] at ht

theorem theta_contact_II_nine_discriminant (ε η : K) (he : ε^2=1) (hh : η^2=1) :
    (ε*η*(-818/81))^2-4*1*1≠0 := by
  norm_num [mul_pow,he,hh]

theorem theta_contact_II_eleven_discriminant (ε η : K) (he : ε^2=1) (hh : η^2=1) :
    (ε*η*(1222/121))^2-4*1*1≠0 := by
  norm_num [mul_pow,he,hh]

theorem theta_contact_III_nine_eleven_discriminant (ε η : K) (he : ε^2=1) (hh : η^2=1) :
    (ε*η*(-980/99))^2-4*1*(-1)≠0 := by
  norm_num [mul_pow,he,hh]

theorem theta_contact_III_eleven_nine_discriminant (ε η : K) (he : ε^2=1) (hh : η^2=1) :
    (ε*η*(980/99))^2-4*1*(-1)≠0 := by
  norm_num [mul_pow,he,hh]

theorem theta_contact_IV_discriminant (t : K) (ht : t^4-100*t^2+1=0) :
    (0:K)^2-4*(-39592*(t^2+1)/79968)*1≠0 := by
  have h := theta_vertical_t_sq_add_one_ne_zero t ht
  have hid : (0:K)^2-4*(-39592*(t^2+1)/79968)*1=(101/51:K)*(t^2+1) := by ring
  rw [hid]
  exact mul_ne_zero (by norm_num) h

theorem theta_bitangent_I_half (u : K) (hu : u^2=1/2) :
    IsThetaBitangent (.affine u 0) := by
  refine ⟨9801,-1/99,0,1,by norm_num,by norm_num,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_I_half u x y hu using 1 <;> ring

theorem theta_bitangent_I_fifty (u : K) (hu : u^2=50) :
    IsThetaBitangent (.affine u 0) := by
  refine ⟨9801,-9899/99,0,1,by norm_num,by norm_num,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_I_fifty u x y hu using 1 <;> ring

theorem theta_bitangent_I_half_swap (u : K) (hu : u^2=1/2) :
    IsThetaBitangent (.affine 0 u) := by
  refine ⟨9801,1,0,-1/99,by norm_num,by norm_num,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_I_half_swap u x y hu using 1 <;> ring

theorem theta_bitangent_I_fifty_swap (u : K) (hu : u^2=50) :
    IsThetaBitangent (.affine 0 u) := by
  refine ⟨9801,1,0,-9899/99,by norm_num,by norm_num,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_I_fifty_swap u x y hu using 1 <;> ring

theorem theta_bitangent_II_nine (ε η : K) (he : ε^2=1) (hh : η^2=1) :
    IsThetaBitangent (.affine (9*ε/14) (9*η/14)) := by
  refine ⟨13122/49,1,ε*η*(-818/81),1,by norm_num,
    theta_contact_II_nine_discriminant ε η he hh,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_II_nine ε η x y he hh using 1 <;> ring

theorem theta_bitangent_II_eleven (ε η : K) (he : ε^2=1) (hh : η^2=1) :
    IsThetaBitangent (.affine (11*ε/14) (11*η/14)) := by
  refine ⟨29282/49,1,ε*η*(1222/121),1,by norm_num,
    theta_contact_II_eleven_discriminant ε η he hh,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_II_eleven ε η x y he hh using 1 <;> ring

theorem theta_bitangent_III_nine_eleven (s ε η : K)
    (hs : s^2=51) (he : ε^2=1) (hh : η^2=1) :
    IsThetaBitangent (.affine (s*ε*9/102) (s*η*11/102)) := by
  refine ⟨6534/17,1,ε*η*(-980/99),-1,by norm_num,
    theta_contact_III_nine_eleven_discriminant ε η he hh,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_III_nine_eleven s ε η x y hs he hh using 1 <;> ring

theorem theta_bitangent_III_eleven_nine (s ε η : K)
    (hs : s^2=51) (he : ε^2=1) (hh : η^2=1) :
    IsThetaBitangent (.affine (s*ε*11/102) (s*η*9/102)) := by
  refine ⟨6534/17,1,ε*η*(980/99),-1,by norm_num,
    theta_contact_III_eleven_nine_discriminant ε η he hh,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_III_eleven_nine s ε η x y hs he hh using 1 <;> ring

theorem theta_bitangent_IV_of_quartic (t : K) (ht : t^4-100*t^2+1=0) :
    IsThetaBitangent (.vertical t) := by
  refine ⟨39984,-39592*(t^2+1)/79968,0,1,by norm_num,
    theta_contact_IV_discriminant t ht,?_⟩
  intro x y
  dsimp [ThetaLine.restrict]
  convert theta_contact_IV_of_quartic t x y ht using 1 <;> ring

theorem theta_vertical_explicit_square (r s ε η : K)
    (hr : r^2=2) (hs : s^2=51) (he : ε^2=1) (hh : η^2=1) :
    (ε*r*(s+7*η)/2)^2=50+7*η*s := by
  simp only [div_pow,mul_pow,he,hr]
  linear_combination (1/2:K)*hs+(49/2:K)*hh

theorem theta_bitangent_IV (r s ε η : K)
    (hr : r^2=2) (hs : s^2=51) (he : ε^2=1) (hh : η^2=1) :
    IsThetaBitangent (.vertical (ε*r*(s+7*η)/2)) :=
  theta_bitangent_IV_of_quartic _ (theta_vertical_quartic_relation _ s η hs hh
    (theta_vertical_explicit_square r s ε η hr hs he hh))

#print axioms theta_contact_I_half
#print axioms theta_contact_I_fifty
#print axioms theta_contact_II_nine
#print axioms theta_contact_II_eleven
#print axioms theta_contact_III_nine_eleven
#print axioms theta_contact_III_eleven_nine
#print axioms theta_contact_IV
#print axioms theta_contact_IV_discriminant
#print axioms theta_bitangent_I_half
#print axioms theta_bitangent_I_fifty
#print axioms theta_bitangent_II_nine
#print axioms theta_bitangent_II_eleven
#print axioms theta_bitangent_III_nine_eleven
#print axioms theta_bitangent_III_eleven_nine
#print axioms theta_bitangent_IV

end FourCorner
