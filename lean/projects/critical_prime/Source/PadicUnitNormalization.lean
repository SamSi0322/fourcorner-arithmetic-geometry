import FourCorner.CommonRootPadicVal
import Mathlib.NumberTheory.Padics.RingHoms

noncomputable section
namespace FourCorner.PadicUnitNormalization
variable {p : ℕ} [Fact p.Prime]

def integral (x : ℚ_[p]) (hv : 0≤x.valuation) : ℤ_[p] :=
  ⟨x,(Padic.norm_le_one_iff_val_nonneg x).mpr hv⟩

lemma residue_zero_of_pos (x : ℚ_[p]) (hv : 0<x.valuation) :
    PadicInt.toZMod (integral x (le_of_lt hv))=0 := by
  have hx : x≠0 := by intro h;simpa [h] using hv
  have hn : ‖integral x (le_of_lt hv)‖<1 := (commonRoot_norm_lt_one_iff hx).mpr hv
  rw [←RingHom.mem_ker,PadicInt.ker_toZMod,IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit (integral x (le_of_lt hv))
  exact PadicInt.not_isUnit_iff.mpr hn

lemma integral_unit (x : ℚ_[p]) (hx : x≠0) (hv : x.valuation=0) :
    IsUnit (integral x (by rw [hv])) := by
  apply PadicInt.isUnit_iff.mpr
  change ‖x‖=1
  rw [Padic.norm_eq_zpow_neg_valuation hx,hv,neg_zero,zpow_zero]

lemma residue_nonzero_of_unit {u : ℤ_[p]} (hu : IsUnit u) : PadicInt.toZMod u≠0 :=
  (hu.map PadicInt.toZMod).ne_zero

lemma normalize_valuation (x : ℚ_[p]) (n : ℕ) (hx : x≠0) (hv : x.valuation=(n:ℤ)) :
    (x/(p:ℚ_[p])^n).valuation=0 := by
  have hp : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [commonRoot_val_div hx (pow_ne_zero n hp),hv,Padic.valuation_pow,Padic.valuation_p,mul_one,sub_self]

def normalize (x : ℚ_[p]) (n : ℕ) (hx : x≠0) (hv : x.valuation=(n:ℤ)) : ℤ_[p] :=
  integral (x/(p:ℚ_[p])^n) (by rw [normalize_valuation x n hx hv])

lemma normalize_coe (x : ℚ_[p]) (n : ℕ) (hx : x≠0) (hv : x.valuation=(n:ℤ)) :
    (normalize x n hx hv:ℚ_[p])=x/(p:ℚ_[p])^n := rfl

lemma normalize_isUnit (x : ℚ_[p]) (n : ℕ) (hx : x≠0) (hv : x.valuation=(n:ℤ)) :
    IsUnit (normalize x n hx hv) := by
  have hp : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact integral_unit _ (div_ne_zero hx (pow_ne_zero n hp)) (normalize_valuation x n hx hv)

lemma normalize_residue_nonzero (x : ℚ_[p]) (n : ℕ) (hx : x≠0) (hv : x.valuation=(n:ℤ)) :
    PadicInt.toZMod (normalize x n hx hv)≠0 := residue_nonzero_of_unit (normalize_isUnit x n hx hv)
end FourCorner.PadicUnitNormalization
#print axioms FourCorner.PadicUnitNormalization.normalize_isUnit
#print axioms FourCorner.PadicUnitNormalization.residue_zero_of_pos
