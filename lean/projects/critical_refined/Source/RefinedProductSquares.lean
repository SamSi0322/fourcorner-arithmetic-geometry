import RefinedPadicSquares

noncomputable section
namespace FourCorner.CriticalRefinedCompletion
variable {p : ℕ} [Fact p.Prime]

def oppositeParameter (A : Fin 4 → ℚ_[p]) (L : ℤ) : ℚ_[p] :=
  (A 0*A 3+A 1*A 2)/(L:ℚ_[p])^2

def normalizedProduct (u : Fin 4 → ℤ_[p]) : ℤ_[p] :=u 0*u 3+u 1*u 2

lemma square_of_unit_residue (hodd : p≠2) (Q : ℤ_[p])
    (hQ : PadicInt.toZMod Q≠0) (hs : IsSquare (PadicInt.toZMod Q)) :
    IsSquare (Q:ℚ_[p]) := by
  obtain ⟨r,hr⟩ := padicInt_isSquare_of_isSquare_residue_unit hodd Q hQ hs
  exact ⟨(r:ℚ_[p]),congrArg (fun z : ℤ_[p]=>(z:ℚ_[p])) hr⟩

/-- Integral numerators whose residues are the SAME nonzero square give both
actual product-square conditions after division by the actual square denominator. -/
theorem two_squares_of_integral_numerator (hodd : p≠2) (Q D : ℤ_[p])
    (hD : D≠0) (hD0 : PadicInt.toZMod D=0)
    (hQ : PadicInt.toZMod (2*Q)≠0) (hs : IsSquare (PadicInt.toZMod (2*Q))) :
    let t : ℚ_[p] := (Q:ℚ_[p])/(D:ℚ_[p])^2
    IsSquare (2*t) ∧ 2*t≠0 ∧ IsSquare (2*(t+1)) ∧ 2*(t+1)≠0 := by
  have hDq : (D:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hD
  have hd2 := pow_ne_zero 2 hDq
  have hres : PadicInt.toZMod (2*(Q+D^2))=PadicInt.toZMod (2*Q) := by
    simp only [map_mul,map_add,map_pow,hD0,zero_pow (by decide : 2≠0),add_zero]
  have hsq0 := square_of_unit_residue hodd (2*Q) hQ hs
  have hsq1 := square_of_unit_residue hodd (2*(Q+D^2)) (by rwa [hres]) (by rwa [hres])
  have hn0 : ((2*Q:ℤ_[p]):ℚ_[p])≠0 :=
    PadicInt.coe_ne_zero.mpr (fun hz=>hQ (by rw [hz,map_zero]))
  have hn1 : ((2*(Q+D^2):ℤ_[p]):ℚ_[p])≠0 :=
    PadicInt.coe_ne_zero.mpr (fun hz=>hQ (by rw [←hres,hz,map_zero]))
  dsimp only
  have he0 : 2*((Q:ℚ_[p])/(D:ℚ_[p])^2)=((2*Q:ℤ_[p]):ℚ_[p])/(D:ℚ_[p])^2 := by
    simp only [PadicInt.coe_mul,(show ((2:ℤ_[p]):ℚ_[p])=2 from rfl)]
    ring
  have he1 : 2*((Q:ℚ_[p])/(D:ℚ_[p])^2+1)=
      ((2*(Q+D^2):ℤ_[p]):ℚ_[p])/(D:ℚ_[p])^2 := by
    simp only [PadicInt.coe_mul,PadicInt.coe_add,PadicInt.coe_pow,(show ((2:ℤ_[p]):ℚ_[p])=2 from rfl)]
    field_simp
    <;> ring
  rw [he0,he1]
  exact ⟨hsq0.div (IsSquare.sq (D:ℚ_[p])),div_ne_zero hn0 hd2,
    hsq1.div (IsSquare.sq (D:ℚ_[p])),div_ne_zero hn1 hd2⟩

/-- The actual opposite parameter for scaled roots has its exact square
normalization. The denominator and the tuple retain their original values. -/
theorem opposite_parameter_normalization (s : ℕ) (u : Fin 4 → ℤ_[p]) (H : ℤ_[p])
    (A : Fin 4 → ℚ_[p]) (L : ℤ)
    (hA : ∀ j,A j=(p:ℚ_[p])^s*(u j:ℚ_[p]))
    (hL : (L:ℚ_[p])=(p:ℚ_[p])^(2*s)*(H:ℚ_[p])) :
    oppositeParameter A L=(normalizedProduct u:ℚ_[p])/
      (((p:ℤ_[p])^s*H:ℤ_[p]):ℚ_[p])^2 := by
  have hp : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold oppositeParameter normalizedProduct
  rw [hA 0,hA 1,hA 2,hA 3,hL]
  simp only [PadicInt.coe_mul,PadicInt.coe_add,PadicInt.coe_pow,PadicInt.coe_natCast]
  have hpow : (p:ℚ_[p])^(2*s)=((p:ℚ_[p])^s)^2 := by
    rw [←pow_mul];congr 1;omega
  rw [hpow]
  field_simp [hp]
  <;> ring

/-- At every positive depth, a signed nonzero square product residue lifts
both literal expressions 2t and2(t+1), and neither expression vanishes. -/
theorem opposite_parameter_two_squares (hodd : p≠2) (s : ℕ) (hs : 1≤s)
    (u : Fin 4 → ℤ_[p]) (H : ℤ_[p]) (hH : IsUnit H)
    (A : Fin 4 → ℚ_[p]) (L : ℤ)
    (hA : ∀ j,A j=(p:ℚ_[p])^s*(u j:ℚ_[p]))
    (hL : (L:ℚ_[p])=(p:ℚ_[p])^(2*s)*(H:ℚ_[p]))
    (hQ : PadicInt.toZMod (2*normalizedProduct u)≠0)
    (hsq : IsSquare (PadicInt.toZMod (2*normalizedProduct u))) :
    IsSquare (2*oppositeParameter A L) ∧ 2*oppositeParameter A L≠0 ∧
      IsSquare (2*(oppositeParameter A L+1)) ∧ 2*(oppositeParameter A L+1)≠0 := by
  let D : ℤ_[p] :=(p:ℤ_[p])^s*H
  have hp : (p:ℤ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hD : D≠0 :=mul_ne_zero (pow_ne_zero s hp) hH.ne_zero
  have hd : PadicInt.toZMod D=0 := by
    simp only [D,map_mul,map_pow,map_natCast,ZMod.natCast_self,zero_pow (by omega : s≠0),zero_mul]
  rw [opposite_parameter_normalization s u H A L hA hL]
  exact two_squares_of_integral_numerator hodd (normalizedProduct u) D hD hd hQ hsq

end FourCorner.CriticalRefinedCompletion
#print axioms FourCorner.CriticalRefinedCompletion.two_squares_of_integral_numerator
#print axioms FourCorner.CriticalRefinedCompletion.opposite_parameter_normalization
#print axioms FourCorner.CriticalRefinedCompletion.opposite_parameter_two_squares
