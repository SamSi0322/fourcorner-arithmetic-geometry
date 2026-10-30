import PrimitivePadicCoordinates

noncomputable section
namespace FourCorner.CriticalNormalizedRadii
variable {p : ℕ} [Fact p.Prime]

/-- The ORIGINAL four completed-field equations in corner order00,10,01,11. -/
def Equations (X Y L : ℤ) (A : Fin 4 → ℚ_[p]) : Prop :=
  A 0^2=(X:ℚ_[p])^2+(Y:ℚ_[p])^2 ∧
  A 1^2=((X:ℚ_[p])-L)^2+(Y:ℚ_[p])^2 ∧
  A 2^2=(X:ℚ_[p])^2+((Y:ℚ_[p])-L)^2 ∧
  A 3^2=((X:ℚ_[p])-L)^2+((Y:ℚ_[p])-L)^2

structure Data (X Y L : ℤ) (s : ℕ) (A : Fin 4 → ℚ_[p]) where
  H : ℤ_[p]
  u : Fin 4 → ℤ_[p]
  H_coe : (H:ℚ_[p])=(L:ℚ_[p])/(p:ℚ_[p])^(2*s)
  u_coe : ∀ j,(u j:ℚ_[p])=A j/(p:ℚ_[p])^s
  H_unit : IsUnit H
  u_unit : ∀ j,IsUnit (u j)
  diff1 : u 1^2-u 0^2=H*((L:ℤ_[p])-2*X)
  diff2 : u 2^2-u 0^2=H*((L:ℤ_[p])-2*Y)
  diff3 : u 3^2-u 0^2=H*(2*(L:ℤ_[p])-2*X-2*Y)

set_option maxHeartbeats 1500000

def normalized_data (X Y L : ℤ) (s : ℕ) (hs : 1≤s) (A : Fin 4 → ℚ_[p])
    (hroot : Equations X Y L A) (hL : (L:ℚ_[p]).valuation=((2*s:ℕ):ℤ))
    (hA : ∀ j,(A j).valuation=(s:ℤ)) : Data X Y L s A := by
  have hLne : (L:ℚ_[p])≠0 := by
    intro hz
    rw [hz,Padic.valuation_zero] at hL
    omega
  have hAne (j : Fin 4) : A j≠0 := by
    intro hz
    have h:=hA j
    rw [hz,Padic.valuation_zero] at h
    omega
  let H:=PadicUnitNormalization.normalize (L:ℚ_[p]) (2*s) hLne hL
  let u:=fun j=>PadicUnitNormalization.normalize (A j) s (hAne j) (hA j)
  have hpne : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p:ℚ_[p])^(2*s)=((p:ℚ_[p])^s)^2 := by
    rw [←pow_mul]
    congr 1
    omega
  refine ⟨H,u,rfl,fun _=>rfl,PadicUnitNormalization.normalize_isUnit _ _ _ _,
    fun _=>PadicUnitNormalization.normalize_isUnit _ _ _ _,?_,?_,?_⟩
  · apply Subtype.ext
    change (A 1/(p:ℚ_[p])^s)^2-(A 0/(p:ℚ_[p])^s)^2=
      ((L:ℚ_[p])/(p:ℚ_[p])^(2*s))*((L:ℚ_[p])-2*X)
    rw [hpow]
    field_simp [hpne]
    linear_combination hroot.2.1-hroot.1
  · apply Subtype.ext
    change (A 2/(p:ℚ_[p])^s)^2-(A 0/(p:ℚ_[p])^s)^2=
      ((L:ℚ_[p])/(p:ℚ_[p])^(2*s))*((L:ℚ_[p])-2*Y)
    rw [hpow]
    field_simp [hpne]
    linear_combination hroot.2.2.1-hroot.1
  · apply Subtype.ext
    change (A 3/(p:ℚ_[p])^s)^2-(A 0/(p:ℚ_[p])^s)^2=
      ((L:ℚ_[p])/(p:ℚ_[p])^(2*s))*(2*(L:ℚ_[p])-2*X-2*Y)
    rw [hpow]
    field_simp [hpne]
    linear_combination hroot.2.2.2-hroot.1
end FourCorner.CriticalNormalizedRadii
#print axioms FourCorner.CriticalNormalizedRadii.normalized_data
