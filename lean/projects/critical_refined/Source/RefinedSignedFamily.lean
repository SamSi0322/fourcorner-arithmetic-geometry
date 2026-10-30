import RefinedSignedLocalData

noncomputable section
namespace FourCorner.CriticalRefinedCompletion
open CriticalRefinedWave27 CriticalCRTWave25
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The witness retains the actual tuple, its exact root valuations, and
EVERY prescribed signed normalized residue, as well as both nonzero squares. -/
def SignedRefinedRoots (p : ℕ) [Fact p.Prime] (s : ℕ)
    (V : Fin 4 → ZMod p) (X Y L : ℤ) : Prop :=
  ∃ u : Fin 4 → ℤ_[p], ∃ A : Fin 4 → ℚ_[p],
    (∀ j,PadicInt.toZMod (u j)=V j ∧ IsUnit (u j)) ∧
    (∀ j,A j=(p:ℚ_[p])^s*(u j:ℚ_[p])) ∧
    (∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ)) ∧
    IsSquare (2*oppositeParameter A L) ∧ 2*oppositeParameter A L≠0 ∧
    IsSquare (2*(oppositeParameter A L+1)) ∧ 2*(oppositeParameter A L+1)≠0

/-- Every prescribed signed unit pattern with square doubled product has
an actual primitive interior family at EVERY positive depth. No finite-field
existence theorem is assumed here beyond the explicit given signed pattern. -/
theorem signed_refined_family (hodd : p≠2) (s : ℕ) (hs : 1≤s)
    (i b : ZMod p) (V : Fin 4 → ZMod p)
    (hsp : SignedPattern i b (V 0) (V 1) (V 2) (V 3))
    (hV : ∀ j,V j≠0) (hprod : IsSquare (2*(V 0*V 3+V 1*V 2))) :
    ∃ X Y a m : ℕ,0<X ∧ 0<Y ∧ 0<a ∧ 0<m ∧
      (∀ k : ℕ,X<denominator a m k ∧ Y<denominator a m k ∧
        Nat.gcd (Nat.gcd X Y) (denominator a m k)=1 ∧
        padicValNat p (denominator a m k)=2*s ∧
        SignedRefinedRoots p s V X Y (denominator a m k)) ∧
      Function.Injective (fun k : ℕ=>((X:ℚ)/denominator a m k,(Y:ℚ)/denominator a m k)) := by
  obtain ⟨x,y,q,hxu,hyu,hfac,hres⟩ := signed_local_radicand_data hodd s hs i b V hsp
  let n : ℕ :=p^(2*s+1)
  have hn : ∀ r∈({p}:Finset ℕ),(fun _ : ℕ=>n) r≠0 := by
    intro r hr
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hpair : Set.Pairwise (↑({p}:Finset ℕ):Set ℕ)
      (Function.onFun Nat.Coprime (fun _ : ℕ=>n)) := by
    intro r hr t ht hrt
    exact (hrt ((Finset.mem_singleton.mp hr).trans (Finset.mem_singleton.mp ht).symm)).elim
  obtain ⟨X,hX,hxc⟩ := positive_integer_crt {p} (fun _ : ℕ=>x) (fun _ : ℕ=>n) hn hpair
  obtain ⟨Y,hY,hyc⟩ := positive_integer_crt {p} (fun _ : ℕ=>y) (fun _ : ℕ=>n) hn hpair
  have hx : (p:ℤ)^(2*s+1)∣(X:ℤ)-x := by simpa only [n,Nat.cast_pow] using hxc p (Finset.mem_singleton_self p)
  have hy : (p:ℤ)^(2*s+1)∣(Y:ℤ)-y := by simpa only [n,Nat.cast_pow] using hyc p (Finset.mem_singleton_self p)
  have hXu : ¬p∣X := by
    intro hd
    have hd' : (p:ℤ)∣(X:ℤ) := by exact_mod_cast hd
    have hpdiv : (p:ℤ)∣(p:ℤ)^(2*s+1) :=dvd_pow_self _ (by omega)
    have hh:=dvd_sub hd' (dvd_trans hpdiv hx)
    exact hxu (by simpa only [sub_sub_cancel] using hh)
  have hcop : ∀ r∈({p}:Finset ℕ),Nat.Coprime ((fun _ : ℕ=>n) r) (Nat.gcd X Y) := by
    intro r hr
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hXu).of_dvd_right
      (Nat.gcd_dvd_left X Y) |>.pow_left _
  obtain ⟨a,m,ha,hm,hall,hinj⟩ := simultaneous_primitive_progression {p}
    (fun _ : ℕ=>p^(2*s)) (fun _ : ℕ=>n) X Y hX hY hn hpair hcop
  refine ⟨X,Y,a,m,hX,hY,ha,hm,?_,?_⟩
  · intro k
    obtain ⟨hXL,hYL,hg,hmod⟩ :=hall k
    have hmodp:=hmod p (Finset.mem_singleton_self p)
    have hL0 : denominator a m k≠0 := by unfold denominator;omega
    have hval : padicValNat p (denominator a m k)=2*s :=exact_depth_of_modEq hL0 hmodp
    have hLc : (p:ℤ)^(2*s+1)∣(denominator a m k:ℤ)-(p:ℤ)^(2*s) := by
      simpa only [n,Nat.cast_pow] using hmodp.symm.dvd
    obtain ⟨q',hfac',hres'⟩ := transport_signed_data s x y ((p:ℤ)^(2*s)) X Y (denominator a m k) q V hx hy hLc hfac hres
    obtain ⟨u,A,hu,hA,hroot⟩ :=signed_four_scaled_roots hodd s _ q' V hV hfac' hres'
    have hLq : ((denominator a m k:ℕ):ℚ_[p])≠0 := by exact_mod_cast hL0
    have hLv : ((denominator a m k:ℕ):ℚ_[p]).valuation=((2*s:ℕ):ℤ) := by
      rw [Padic.valuation_natCast,hval]
    let H:=PadicUnitNormalization.normalize ((denominator a m k:ℕ):ℚ_[p]) (2*s) hLq hLv
    have hH : IsUnit H :=PadicUnitNormalization.normalize_isUnit _ _ _ _
    have hp : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hLf : ((denominator a m k:ℕ):ℚ_[p])=(p:ℚ_[p])^(2*s)*(H:ℚ_[p]) := by
      change _=(p:ℚ_[p])^(2*s)*(((denominator a m k:ℕ):ℚ_[p])/(p:ℚ_[p])^(2*s))
      field_simp [hp]
    have hrN : PadicInt.toZMod (2*normalizedProduct u)=2*(V 0*V 3+V 1*V 2) := by
      simp only [normalizedProduct,map_mul,map_add,map_ofNat,(hu 0).2.1,(hu 1).2.1,(hu 2).2.1,(hu 3).2.1]
    have h2 : (2:ZMod p)≠0 :=Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hodd)
    have hN : PadicInt.toZMod (2*normalizedProduct u)≠0 := by
      rw [hrN]
      exact mul_ne_zero h2 (signed_product_nonzero hsp).1
    have hpairs:=opposite_parameter_two_squares hodd s hs u H hH A (denominator a m k) hA
      (by simpa only [Int.cast_natCast] using hLf) hN (by rwa [hrN])
    exact ⟨hXL,hYL,hg,hval,u,A,fun j=>⟨(hu j).2.1,(hu j).2.2⟩,hA,hroot,hpairs⟩
  · intro j k he
    exact hinj (congrArg Prod.fst he)
end FourCorner.CriticalRefinedCompletion
#print axioms FourCorner.CriticalRefinedCompletion.signed_refined_family
