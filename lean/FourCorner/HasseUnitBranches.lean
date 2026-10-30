import FourCorner.HasseDyadicBranches
import FourCorner.ThetaLocalHensel
namespace FourCorner.HasseUnitBranches
private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide⟩
open HasseDyadicNorm HasseDyadicSource HasseDyadicBranches

theorem square_one_add_of_val_ge_three (t : ℚ_[2]) (ht : 3 ≤ t.valuation) :
    IsSquare (1+t) := by
  have ht0 : t ≠ 0 := by intro hh; simp [hh] at ht
  apply padic_isSquare_one_add
  rw [Padic.norm_eq_zpow_neg_valuation ht0,
    show ‖(2 : ℚ_[2])‖=(1/2:ℝ) by simpa using (Padic.norm_p (p:=2))]
  have hh : (2:ℝ)^(-t.valuation) < (2:ℝ)^(-2:ℤ) :=
    (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mpr (by omega)
  norm_num at hh ⊢
  exact hh

theorem unit_neighbor_odd (p r : ℚ_[2]) (hr : r ≠ 0)
    (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (hc : r-1 ≠ 0) (hd : r+1 ≠ 0)
    (hrv : r.valuation ≠ 0) (her : Even r.valuation)
    (h1 : IsSquare (2*(p-1)*(r-1)))
    (h2 : IsSquare (2*(p+1)*(r+1))) :
    Odd (p-1).valuation ∧ Odd (p+1).valuation := by
  obtain ⟨hv1,hv2⟩ := neighbor_vals hr hrv
  have hem : Even (min r.valuation 0) := by
    rcases le_total r.valuation 0 with h | h
    · rw [min_eq_left h]; exact her
    · rw [min_eq_right h]; exact ⟨0,by simp⟩
  obtain ⟨k,hk⟩ := hem
  constructor
  · obtain ⟨j,hj⟩ := commonRoot_even_val_of_isSquare h1
    rw [Padic.valuation_mul (mul_ne_zero (by norm_num) ha) hc,
      Padic.valuation_mul (by norm_num) ha,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,hv1] at hj
    exact ⟨j-k-1,by omega⟩
  · obtain ⟨j,hj⟩ := commonRoot_even_val_of_isSquare h2
    rw [Padic.valuation_mul (mul_ne_zero (by norm_num) hb) hd,
      Padic.valuation_mul (by norm_num) hb,
      show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p,hv2] at hj
    exact ⟨j-k-1,by omega⟩

theorem product_square_class (p r : ℚ_[2]) (hr : r ≠ 0)
    (hc : r-1 ≠ 0) (hd : r+1 ≠ 0) (her : Even r.valuation)
    (h1 : IsSquare (2*(p-1)*(r-1))) (h2 : IsSquare (2*(p+1)*(r+1))) :
    (r.valuation<0 → IsSquare ((p-1)*(p+1))) ∧
    (0<r.valuation → IsSquare (-((p-1)*(p+1)))) := by
  have hprod : IsSquare (4*((p-1)*(p+1))*(r^2-1)) := by
    have hh := h1.mul h2
    have he : (2*(p-1)*(r-1))*(2*(p+1)*(r+1)) =
        4*((p-1)*(p+1))*(r^2-1) := by ring
    rwa [he] at hh
  have hprod' : IsSquare (((p-1)*(p+1))*(r^2-1)) := by
    have hh := hprod.div (IsSquare.sq (2 : ℚ_[2]))
    have he : (4*((p-1)*(p+1))*(r^2-1))/(2^2) =
        ((p-1)*(p+1))*(r^2-1) := by ring
    rwa [he] at hh
  have hdne : r^2-1 ≠ 0 := by
    rw [show r^2-1=(r-1)*(r+1) by ring]
    exact mul_ne_zero hc hd
  obtain ⟨k,hk⟩ := her
  constructor
  · intro hneg
    have ht0 : -(1/r^2) ≠ 0 := neg_ne_zero.mpr (div_ne_zero one_ne_zero (pow_ne_zero _ hr))
    have htv : (-(1/r^2)).valuation= -2*r.valuation := by
      rw [commonRoot_val_neg,commonRoot_val_div one_ne_zero (pow_ne_zero _ hr),
        Padic.valuation_one,Padic.valuation_pow]; ring
    have hsq := square_one_add_of_val_ge_three (-(1/r^2)) (by rw [htv]; omega)
    have hD : IsSquare (r^2-1) := by
      have hh := (IsSquare.sq r).mul hsq
      have he : r^2*(1+ -(1/r^2))=r^2-1 := by field_simp <;> ring
      rwa [he] at hh
    have hh := hprod'.div hD
    have he : (((p-1)*(p+1))*(r^2-1))/(r^2-1) = (p-1)*(p+1) := by field_simp
    rwa [he] at hh
  · intro hpos
    have htv : (-r^2).valuation=2*r.valuation := by
      rw [commonRoot_val_neg,Padic.valuation_pow]; simp
    have hsq := square_one_add_of_val_ge_three (-r^2) (by rw [htv]; omega)
    have hD : IsSquare (-(r^2-1)) := by
      have he : 1+ -r^2= -(r^2-1) := by ring
      rwa [he] at hsq
    have hh := hprod'.div hD
    have he : (((p-1)*(p+1))*(r^2-1))/(-(r^2-1)) = -((p-1)*(p+1)) := by field_simp
    rwa [he] at hh

theorem source_r_sign (p r : ℚ_[2]) (hr : r ≠ 0)
    (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (hrv : r.valuation ≠ 0) (her : Even r.valuation)
    (h3 : IsSquare ((p-1)*r+p+1)) :
    (4 ≤ (p-1).valuation → (p+1).valuation=1 → r.valuation<0) ∧
    ((p-1).valuation=1 → 4 ≤ (p+1).valuation → 0<r.valuation) := by
  have hf : (p-1)*r+p+1=(p-1)*r+(p+1) := by ring
  have hvm : ((p-1)*r).valuation=(p-1).valuation+r.valuation := Padic.valuation_mul ha hr
  obtain ⟨k,hk⟩ := her
  obtain ⟨j,hj⟩ := commonRoot_even_val_of_isSquare h3
  constructor
  · intro hva hvb
    by_contra hh
    have hrpos : 0<r.valuation := by omega
    have hvf : ((p-1)*r+p+1).valuation=1 := by
      rw [hf,commonRoot_val_add_of_ne (mul_ne_zero ha hr) hb
        (show ((p-1)*r).valuation ≠ (p+1).valuation by rw [hvm,hvb]; omega),hvm,hvb]
      exact min_eq_right (by omega)
    omega
  · intro hva hvb
    by_contra hh
    have hrneg : r.valuation<0 := by omega
    have hvf : ((p-1)*r+p+1).valuation=1+r.valuation := by
      rw [hf,commonRoot_val_add_of_ne (mul_ne_zero ha hr) hb
        (show ((p-1)*r).valuation ≠ (p+1).valuation by rw [hvm,hva]; omega),hvm,hva]
      exact min_eq_left (by omega)
    omega

/-- The p=1 mod16 unit branch has exactly the claimed square class and depth. -/
theorem unit_one_branch (P : ℤ_[2]) (r : ℚ_[2])
    (hp : (P : ℚ_[2]) ≠ 0) (hr : r ≠ 0)
    (ha : (P : ℚ_[2])-1 ≠ 0) (hb : (P : ℚ_[2])+1 ≠ 0)
    (hc : r-1 ≠ 0) (hd : r+1 ≠ 0)
    (h0 : IsSquare ((P : ℚ_[2])*r))
    (h1 : IsSquare (2*((P : ℚ_[2])-1)*(r-1)))
    (h2 : IsSquare (2*((P : ℚ_[2])+1)*(r+1)))
    (h3 : IsSquare (((P : ℚ_[2])-1)*r+(P : ℚ_[2])+1))
    (hres : PadicInt.toZModPow 4 P=1) :
    IsSquare (((P : ℚ_[2])-1)/2) ∧ Odd ((P : ℚ_[2])-1).valuation ∧
      5 ≤ ((P : ℚ_[2])-1).valuation := by
  let p : ℚ_[2] := P
  change p ≠ 0 at hp
  change p-1 ≠ 0 at ha
  change p+1 ≠ 0 at hb
  change IsSquare (p*r) at h0
  change IsSquare (2*(p-1)*(r-1)) at h1
  change IsSquare (2*(p+1)*(r+1)) at h2
  change IsSquare ((p-1)*r+p+1) at h3
  change IsSquare ((p-1)/2) ∧ Odd (p-1).valuation ∧ 5 ≤ (p-1).valuation
  have hpv : p.valuation=0 := val_zero_of_residue_one_or_fifteen P (Or.inl hres)
  have hva : 4 ≤ (p-1).valuation := by
    apply valuation_ge_of_residue_zero (P-1) ha 4
    simp only [map_sub,map_one,hres,sub_self]
  have hvb : (p+1).valuation=1 := by
    have hh := commonRoot_val_add_of_ne ha (by norm_num : (2 : ℚ_[2]) ≠ 0)
      (show (p-1).valuation ≠ (2 : ℚ_[2]).valuation by rw [show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]; omega)
    have hid : p-1+2=p+1 := by ring
    rw [hid,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p] at hh
    exact hh.trans (min_eq_right (by omega))
  have hR : r.valuation ≠ 0 ∧ Even r.valuation := by
    rcases valuation_dichotomy p r hp hr ha hb hc hd h0 h1 h2 h3 with hh | hh
    · exact hh.2
    · exact False.elim (hh.2.1 hpv)
  have hodd := (unit_neighbor_odd p r hr ha hb hc hd hR.1 hR.2 h1 h2).1
  have hrneg := (source_r_sign p r hr ha hb hR.1 hR.2 h3).1 hva hvb
  have habsq := (product_square_class p r hr hc hd hR.2 h1 h2).1 hrneg
  have hb2 : IsSquare ((p+1)/2) := by
    have hval : 3 ≤ ((p-1)/2).valuation := by
      rw [commonRoot_val_div ha (by norm_num),show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
      omega
    have hh := square_one_add_of_val_ge_three ((p-1)/2) hval
    have hid : 1+(p-1)/2=(p+1)/2 := by ring
    rwa [hid] at hh
  have ha2 : IsSquare ((p-1)/2) := by
    have hh := (habsq.mul hb2).div (IsSquare.sq (p+1))
    have hid : (((p-1)*(p+1))*((p+1)/2))/(p+1)^2=(p-1)/2 := by field_simp [hb] <;> ring
    rwa [hid] at hh
  refine ⟨ha2,hodd,?_⟩
  obtain ⟨k,hk⟩ := hodd
  omega

/-- The p=15 mod16 unit branch has exactly the claimed square class and depth. -/
theorem unit_fifteen_branch (P : ℤ_[2]) (r : ℚ_[2])
    (hp : (P : ℚ_[2]) ≠ 0) (hr : r ≠ 0)
    (ha : (P : ℚ_[2])-1 ≠ 0) (hb : (P : ℚ_[2])+1 ≠ 0)
    (hc : r-1 ≠ 0) (hd : r+1 ≠ 0)
    (h0 : IsSquare ((P : ℚ_[2])*r))
    (h1 : IsSquare (2*((P : ℚ_[2])-1)*(r-1)))
    (h2 : IsSquare (2*((P : ℚ_[2])+1)*(r+1)))
    (h3 : IsSquare (((P : ℚ_[2])-1)*r+(P : ℚ_[2])+1))
    (hres : PadicInt.toZModPow 4 P=15) :
    IsSquare (((P : ℚ_[2])+1)/2) ∧ Odd ((P : ℚ_[2])+1).valuation ∧
      5 ≤ ((P : ℚ_[2])+1).valuation := by
  let p : ℚ_[2] := P
  change p ≠ 0 at hp
  change p-1 ≠ 0 at ha
  change p+1 ≠ 0 at hb
  change IsSquare (p*r) at h0
  change IsSquare (2*(p-1)*(r-1)) at h1
  change IsSquare (2*(p+1)*(r+1)) at h2
  change IsSquare ((p-1)*r+p+1) at h3
  change IsSquare ((p+1)/2) ∧ Odd (p+1).valuation ∧ 5 ≤ (p+1).valuation
  have hpv : p.valuation=0 := val_zero_of_residue_one_or_fifteen P (Or.inr hres)
  have hvb : 4 ≤ (p+1).valuation := by
    apply valuation_ge_of_residue_zero (P+1) hb 4
    simp only [map_add,map_one,hres]
    decide
  have hva : (p-1).valuation=1 := by
    have hh := commonRoot_val_sub_of_ne hb (by norm_num : (2 : ℚ_[2]) ≠ 0)
      (show (p+1).valuation ≠ (2 : ℚ_[2]).valuation by rw [show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]; omega)
    have hid : p+1-2=p-1 := by ring
    rw [hid,show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p] at hh
    exact hh.trans (min_eq_right (by omega))
  have hR : r.valuation ≠ 0 ∧ Even r.valuation := by
    rcases valuation_dichotomy p r hp hr ha hb hc hd h0 h1 h2 h3 with hh | hh
    · exact hh.2
    · exact False.elim (hh.2.1 hpv)
  have hodd := (unit_neighbor_odd p r hr ha hb hc hd hR.1 hR.2 h1 h2).2
  have hrpos := (source_r_sign p r hr ha hb hR.1 hR.2 h3).2 hva hvb
  have habsq := (product_square_class p r hr hc hd hR.2 h1 h2).2 hrpos
  have ha2 : IsSquare (-((p-1)/2)) := by
    have hval : 3 ≤ (-((p+1)/2)).valuation := by
      rw [commonRoot_val_neg,commonRoot_val_div hb (by norm_num),
        show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p]
      omega
    have hh := square_one_add_of_val_ge_three (-((p+1)/2)) hval
    have hid : 1+ -((p+1)/2)= -((p-1)/2) := by ring
    rwa [hid] at hh
  have hb2 : IsSquare ((p+1)/2) := by
    have hh := (habsq.mul ha2).div (IsSquare.sq (p-1))
    have hid : ((-((p-1)*(p+1)))*(-((p-1)/2)))/(p-1)^2=(p+1)/2 := by field_simp [ha] <;> ring
    rwa [hid] at hh
  refine ⟨hb2,hodd,?_⟩
  obtain ⟨k,hk⟩ := hodd
  omega

#print axioms unit_one_branch
#print axioms unit_fifteen_branch
#print axioms square_one_add_of_val_ge_three
#print axioms unit_neighbor_odd
#print axioms product_square_class
end FourCorner.HasseUnitBranches
