import RationalFormalDepth
import ActualDyadicCharacter15
import CSLogSupport.CommonSourceDyadicResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace FourCorner.CommonSource

/-- Canonical transport of the actual integral formal parameter to Z_2. -/
def usualScaledParameter (n : ℤ) (hn : n ≠ 0) (k : ℕ) (P : Hlevel n hn k) : ℤ_[2] :=
  dyadicIntegerEquiv15.symm (rationalScaledParameter15 n hn k P)

theorem usualScaledParameter_coordinate (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (P : Hlevel n hn k) (x y : ℚ)
    (h : (congruentCurve (n:ℚ)).toAffine.Nonsingular x y)
    (hP : (P : Point (n:ℚ)) = .some x y h) :
    (usualScaledParameter n hn k P : ℚ_[2]) = (-(x:ℚ_[2])/y)/2^(k+1) := by
  have hc := rationalScaledParameter_coordinate15 n hn k P x y h hP
  have hh := congrArg (Padic.adicCompletionEquiv ℤ ⟨2,Nat.prime_two⟩).symm hc
  have he := PadicInt.coe_adicCompletionIntegersEquiv_symm_apply ℤ ⟨2,Nat.prime_two⟩
    (rationalScaledParameter15 n hn k P)
  change (usualScaledParameter n hn k P : ℚ_[2]) = _ at he
  rw [he]
  have htwo : (Padic.adicCompletionEquiv ℤ ⟨2,Nat.prime_two⟩).symm (2:DyadicField) = 2 := map_ofNat _ 2
  simpa [htwo] using hh

theorem usualScaledParameter_residue (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (P : Hlevel n hn k) :
    rationalDyadicCharacter15 n hn k hk P = commonSourceResidueFour (usualScaledParameter n hn k P) := rfl

/-- The proved rational mod-four character takes equal-depth nonzero points to
values agreeing up to sign, at every permitted common depth. -/
theorem actual_character_sign_of_equal_depth (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (P Q : Hlevel n hn k) (x y w z : ℚ)
    (hPxy : (congruentCurve (n:ℚ)).toAffine.Nonsingular x y)
    (hQwz : (congruentCurve (n:ℚ)).toAffine.Nonsingular w z)
    (hP : (P : Point (n:ℚ)) = .some x y hPxy)
    (hQ : (Q : Point (n:ℚ)) = .some w z hQwz)
    (hv : padicValRat 2 x=padicValRat 2 w) :
    rationalDyadicCharacter15 n hn k hk P = rationalDyadicCharacter15 n hn k hk Q ∨
    rationalDyadicCharacter15 n hn k hk P = -rationalDyadicCharacter15 n hn k hk Q := by
  have hp_mem := P.property
  have hq_mem := Q.property
  rw [hP] at hp_mem
  rw [hQ] at hq_mem
  obtain ⟨hx0,hxv⟩ := (some_mem_Hlevel_iff n hn k x y hPxy).mp hp_mem
  obtain ⟨hw0,hwv⟩ := (some_mem_Hlevel_iff n hn k w z hQwz).mp hq_mem
  have heP := (congruentEquation_iff_weierstrass (n:ℚ) x y).mpr hPxy.left
  have heQ := (congruentEquation_iff_weierstrass (n:ℚ) w z).mpr hQwz.left
  obtain ⟨hp,hq,hdepth⟩ := rational_formal_depth n heP heQ (by omega) (by omega) hv
  rw [usualScaledParameter_residue,usualScaledParameter_residue]
  exact scaled_residue_sign (usualScaledParameter n hn k P) (usualScaledParameter n hn k Q)
    _ _ k hp hq hdepth
    (usualScaledParameter_coordinate n hn k P x y hPxy hP)
    (usualScaledParameter_coordinate n hn k Q w z hQwz hQ)

#print axioms usualScaledParameter_coordinate
#print axioms actual_character_sign_of_equal_depth
end FourCorner.CommonSource
