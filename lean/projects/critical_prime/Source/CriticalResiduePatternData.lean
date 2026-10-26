import CriticalNormalizedRadii

noncomputable section
namespace FourCorner.CriticalResiduePatternData
open CriticalNormalizedRadii
variable {p : ℕ} [Fact p.Prime]

def radius {X Y L : ℤ} {s : ℕ} {A : Fin 4 → ℚ_[p]} (D : Data X Y L s A) (j : Fin 4) : ZMod p :=
  PadicInt.toZMod (D.u j)
def iota (X Y : ℤ) : ZMod p := (Y:ZMod p)/(X:ZMod p)
def step {X Y L : ℤ} {s : ℕ} {A : Fin 4 → ℚ_[p]} (D : Data X Y L s A) : ZMod p :=
  -2*PadicInt.toZMod D.H*(X:ZMod p)

set_option maxHeartbeats 1500000

theorem pattern_data (hodd : p≠2) (X Y L : ℤ) (s : ℕ) (hs : 1≤s) (A : Fin 4 → ℚ_[p])
    (hprim : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1)
    (hroot : Equations X Y L A) (hL : (L:ℚ_[p]).valuation=((2*s:ℕ):ℤ))
    (hA : ∀ j,(A j).valuation=(s:ℤ)) :
    let D:=normalized_data X Y L s hs A hroot hL hA
    (X:ZMod p)≠0 ∧ (Y:ZMod p)≠0 ∧ iota (p:=p) X Y^2= -1 ∧ step D≠0 ∧
      (∀ j,radius D j≠0) ∧
      radius D 1^2=radius D 0^2+step D ∧
      radius D 2^2=radius D 0^2+iota X Y*step D ∧
      radius D 3^2=radius D 0^2+(1+iota X Y)*step D := by
  let D:=normalized_data X Y L s hs A hroot hL hA
  have hLpos : 0<(L:ℚ_[p]).valuation := by rw [hL];omega
  have hL0 : (L:ZMod p)=0:=PrimitivePadicCoordinates.integer_residue_zero L hLpos
  have hApos : 0<(A 0).valuation := by rw [hA];omega
  have hnorm:=PrimitivePadicCoordinates.norm_residue_zero X Y (A 0) hroot.1 hApos
  obtain ⟨hx,hy⟩:=PrimitivePadicCoordinates.coordinate_residues_nonzero X Y L hprim hL0 hnorm
  have hi : iota (p:=p) X Y^2= -1 := by
    dsimp [iota]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hx)).mpr
    linear_combination hnorm
  have h2 : (2:ZMod p)≠0:=Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hodd)
  have hH : PadicInt.toZMod D.H≠0:=PadicUnitNormalization.residue_nonzero_of_unit D.H_unit
  have hb : step D≠0:=mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hH) hx
  have hr (j : Fin 4) : radius D j≠0:=PadicUnitNormalization.residue_nonzero_of_unit (D.u_unit j)
  have hib : iota (p:=p) X Y*step D= -2*PadicInt.toZMod D.H*(Y:ZMod p) := by
    dsimp [iota,step]
    field_simp [hx]
  have hsum : (1+iota (p:=p) X Y)*step D=
      -2*PadicInt.toZMod D.H*(X:ZMod p)-2*PadicInt.toZMod D.H*(Y:ZMod p) := by
    rw [add_mul,one_mul,hib]
    dsimp [step]
    ring
  have h1:=congrArg PadicInt.toZMod D.diff1
  have h2r:=congrArg PadicInt.toZMod D.diff2
  have h3:=congrArg PadicInt.toZMod D.diff3
  simp only [map_sub,map_pow,map_mul,map_intCast,map_ofNat,hL0] at h1 h2r h3
  refine ⟨hx,hy,hi,hb,hr,?_,?_,?_⟩
  · dsimp only [radius,step]
    linear_combination h1
  · rw [hib]
    dsimp only [radius]
    linear_combination h2r
  · rw [hsum]
    dsimp only [radius]
    linear_combination h3
end FourCorner.CriticalResiduePatternData
#print axioms FourCorner.CriticalResiduePatternData.pattern_data
