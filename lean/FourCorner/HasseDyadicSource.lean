import FourCorner.CommonRootDyadicUnitPair
import FourCorner.PadicResidueSquareBasic
import FourCorner.CommonRootDyadicResidues
import Mathlib.Tactic
namespace FourCorner.HasseDyadicSource
private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide⟩

def SquareResidue16 (r : ZMod 16) : Prop := r=0 ∨ r=1 ∨ r=4 ∨ r=9
instance (r : ZMod 16) : Decidable (SquareResidue16 r) := inferInstanceAs
  (Decidable (r=0 ∨ r=1 ∨ r=4 ∨ r=9))
theorem square_residue16 (r : ZMod 16) (hr : IsSquare r) : SquareResidue16 r := by
  obtain ⟨x,hx⟩ := hr
  rw [hx]
  have hf : ∀ x : ZMod 16, SquareResidue16 (x*x) := by decide
  exact hf x

theorem integral_square_residue16 (r : ℤ_[2]) (hr : IsSquare (r : ℚ_[2])) :
    SquareResidue16 (PadicInt.toZModPow 4 r) := by
  apply square_residue16
  exact ((padicInt_isSquare_coe_iff r).mp hr).map (PadicInt.toZModPow 4)

theorem no_unit_pair (p r : ℚ_[2]) (hp : ‖p‖=1) (hr : ‖r‖=1)
    (h0 : IsSquare (p*r)) (h1 : IsSquare (2*(p-1)*(r-1)))
    (h2 : IsSquare (2*(p+1)*(r+1))) : False := by
  let P : ℤ_[2] := ⟨p,hp.le⟩
  let R : ℤ_[2] := ⟨r,hr.le⟩
  have hp2 := (dyadic_norm_one_iff_residue_ne_zero P).mp hp
  have hr2 := (dyadic_norm_one_iff_residue_ne_zero R).mp hr
  have hP : (ZMod.castHom (by decide : 2 ∣ 16) (ZMod 2))
      (PadicInt.toZModPow 4 P) ≠ 0 := by
    have hh := PadicInt.cast_toZModPow (p:=2) 1 4 (by decide) P
    simpa only [ZMod.castHom_apply] using hh.trans_ne hp2
  have hR : (ZMod.castHom (by decide : 2 ∣ 16) (ZMod 2))
      (PadicInt.toZModPow 4 R) ≠ 0 := by
    have hh := PadicInt.cast_toZModPow (p:=2) 1 4 (by decide) R
    simpa only [ZMod.castHom_apply] using hh.trans_ne hr2
  have h0r := integral_square_residue16 (P*R) h0
  have h1r := integral_square_residue16 (2*(P-1)*(R-1)) h1
  have h2r := integral_square_residue16 (2*(P+1)*(R+1)) h2
  simp only [map_mul,map_sub,map_add,map_one,map_ofNat] at h0r h1r h2r
  have hf : ∀ P R : ZMod 16,
      (ZMod.castHom (by decide : 2 ∣ 16) (ZMod 2)) P ≠ 0 →
      (ZMod.castHom (by decide : 2 ∣ 16) (ZMod 2)) R ≠ 0 →
      SquareResidue16 (P*R) → SquareResidue16 (2*(P-1)*(R-1)) →
      SquareResidue16 (2*(P+1)*(R+1)) → False := by decide
  exact hf _ _ hP hR h0r h1r h2r

/-- Every valuation of p±1 away from the unit branch, with no bound on depth. -/
theorem neighbor_vals {p : ℚ_[2]} (hp : p ≠ 0) (hv : p.valuation ≠ 0) :
    (p-1).valuation=min p.valuation 0 ∧
    (p+1).valuation=min p.valuation 0 := by
  have hne : p.valuation ≠ (1 : ℚ_[2]).valuation := by simpa using hv
  constructor
  · simpa only [Padic.valuation_one] using commonRoot_val_sub_of_ne hp one_ne_zero hne
  · simpa only [Padic.valuation_one] using commonRoot_val_add_of_ne hp one_ne_zero hne

/-- Four-square sources cannot have both parameter valuations nonzero.
Only the three original middle/first/fourth square conditions are used. -/
theorem not_both_nonzero (p r : ℚ_[2])
    (hp : p ≠ 0) (hr : r ≠ 0)
    (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (hc : r-1 ≠ 0) (hd : r+1 ≠ 0)
    (h0 : IsSquare (p*r)) (h1 : IsSquare (2*(p-1)*(r-1)))
    (h3 : IsSquare ((p-1)*r+p+1))
    (hpv : p.valuation ≠ 0) (hrv : r.valuation ≠ 0) : False := by
  obtain ⟨k,hk⟩ := commonRoot_even_val_of_isSquare h0
  rw [Padic.valuation_mul hp hr] at hk
  obtain ⟨j,hj⟩ := commonRoot_even_val_of_isSquare h1
  rw [Padic.valuation_mul (mul_ne_zero (by norm_num) ha) hc,
    Padic.valuation_mul (by norm_num) ha,
    show (2 : ℚ_[2]).valuation=1 from Padic.valuation_p] at hj
  obtain ⟨hva,hvb⟩ := neighbor_vals hp hpv
  obtain ⟨hvc,hvd⟩ := neighbor_vals hr hrv
  rw [hva,hvc] at hj
  rcases lt_or_gt_of_ne hpv with hpneg | hppos
  · rcases lt_or_gt_of_ne hrv with hrneg | hrpos
    · rw [min_eq_left hpneg.le,min_eq_left hrneg.le] at hj
      omega
    · rw [min_eq_left hpneg.le,min_eq_right hrpos.le] at hj
      have hf : (p-1)*r+p+1 = p*(r+1)+(1-r) := by ring
      have hval1 : (p*(r+1)).valuation=p.valuation := by
        rw [Padic.valuation_mul hp hd,hvd,min_eq_right hrpos.le,add_zero]
      have hval2 : (1-r).valuation=0 := by
        rw [show 1-r= -(r-1) by ring,commonRoot_val_neg,hvc,min_eq_right hrpos.le]
      have hfval : ((p-1)*r+p+1).valuation=p.valuation := by
        rw [hf,commonRoot_val_add_of_ne (mul_ne_zero hp hd)
          (sub_ne_zero.mpr (by intro h; exact hc (sub_eq_zero.mpr h.symm)))
          (show (p*(r+1)).valuation ≠ (1-r).valuation by rw [hval1,hval2]; omega),
          hval1,hval2,min_eq_left hpneg.le]
      obtain ⟨l,hl⟩ := commonRoot_even_val_of_isSquare h3
      rw [hfval] at hl
      omega
  · rcases lt_or_gt_of_ne hrv with hrneg | hrpos
    · rw [min_eq_right hppos.le,min_eq_left hrneg.le] at hj
      have hval1 : ((p-1)*r).valuation=r.valuation := by
        rw [Padic.valuation_mul ha hr,hva,min_eq_right hppos.le,zero_add]
      have hval2 : (p+1).valuation=0 := by rw [hvb,min_eq_right hppos.le]
      have hf : (p-1)*r+p+1 = (p-1)*r+(p+1) := by ring
      have hfval : ((p-1)*r+p+1).valuation=r.valuation := by
        rw [hf,commonRoot_val_add_of_ne (mul_ne_zero ha hr) hb
          (show ((p-1)*r).valuation ≠ (p+1).valuation by rw [hval1,hval2]; omega),
          hval1,hval2,min_eq_left hrneg.le]
      obtain ⟨l,hl⟩ := commonRoot_even_val_of_isSquare h3
      rw [hfval] at hl
      omega
    · rw [min_eq_right hppos.le,min_eq_right hrpos.le] at hj
      omega

/-- Complete unrestricted valuation dichotomy for the actual four radicands. -/
theorem valuation_dichotomy (p r : ℚ_[2])
    (hp : p ≠ 0) (hr : r ≠ 0)
    (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (hc : r-1 ≠ 0) (hd : r+1 ≠ 0)
    (h0 : IsSquare (p*r)) (h1 : IsSquare (2*(p-1)*(r-1)))
    (h2 : IsSquare (2*(p+1)*(r+1))) (h3 : IsSquare ((p-1)*r+p+1)) :
    (p.valuation=0 ∧ r.valuation ≠ 0 ∧ Even r.valuation) ∨
    (r.valuation=0 ∧ p.valuation ≠ 0 ∧ Even p.valuation) := by
  have he : Even (p.valuation+r.valuation) := by
    have hh := commonRoot_even_val_of_isSquare h0
    rwa [Padic.valuation_mul hp hr] at hh
  by_cases hpv : p.valuation=0
  · have hrv : r.valuation ≠ 0 := by
      intro hrv
      apply no_unit_pair p r _ _ h0 h1 h2
      · rw [Padic.norm_eq_zpow_neg_valuation hp,hpv]; simp
      · rw [Padic.norm_eq_zpow_neg_valuation hr,hrv]; simp
    exact Or.inl ⟨hpv,hrv,by simpa [hpv] using he⟩
  · have hrv : r.valuation=0 := by
      by_contra hrv
      exact not_both_nonzero p r hp hr ha hb hc hd h0 h1 h3 hpv hrv
    exact Or.inr ⟨hrv,hpv,by simpa [hrv] using he⟩
#print axioms no_unit_pair
#print axioms valuation_dichotomy
end FourCorner.HasseDyadicSource
