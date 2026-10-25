import FiniteHenselRealization

noncomputable section
namespace FourCorner.InfinityHenselRealization
open RadicalLinearization PadicUnitNeighbourhood
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- The four genuine unit functions P/Z,C/Z,M,B, written in u=1/Z. -/
def values {R : Type*} [CommRing R] (t κ ki u : R) : Fin 4 → R
  | 0 => κ+(t+1)*u^2
  | 1 => κ-(t-1)*u^2
  | 2 => -(t-1)+(t-1)*(t+1)*ki*u^2
  | 3 => t+1+(t-1)*(t+1)*ki*u^2

def constantValues {R : Type*} [CommRing R] (t κ : R) : Fin 4 → R
  | 0 => κ
  | 1 => κ
  | 2 => -(t-1)
  | 3 => t+1

def recovered {L : Type*} [Field L] (u : L) (r : Fin 4 → L) : Fin 5 → L
  | 0 => r 0/u
  | 1 => r 1/u
  | 2 => r 2/u
  | 3 => r 3/u
  | 4 => u⁻¹

theorem recovered_squares {L : Type*} [Field L] (t κ u : L) (hκ : κ ≠ 0) (hu : u ≠ 0)
    (r : Fin 4 → L) (hr : ∀ i, r i^2 = values t κ κ⁻¹ u i) (i : Fin 5) :
    recovered u r i^2 = RadicalLinearization.values t κ⁻¹ (κ/u^2) i := by
  fin_cases i <;> dsimp only [recovered]
  all_goals try rw [div_pow,hr]
  all_goals simp only [values,RadicalLinearization.values]
  all_goals field_simp [hκ,hu] <;> ring

/-- Actual Hensel realization of the infinity chart. The three square-unit
conditions must come from the chosen residue place; they are not postulated
as a conclusion about all residue fields or a characteristic-zero model. -/
theorem realize (hp : p ≠ 2) (t κ : ℚ) (hκ : κ ≠ 0) (T K KI : ℤ_[p])
    (hT : (T : ℚ_[p]) = t) (hK : (K : ℚ_[p]) = κ)
    (hKI : (KI : ℚ_[p]) = (κ : ℚ_[p])⁻¹)
    (hu : ∀ i, PadicInt.toZMod (constantValues T K i) ≠ 0)
    (hs : ∀ i, IsSquare (PadicInt.toZMod (constantValues T K i))) :
    ∃ (e : ℚ_[p]) (r : Fin 5 → ℚ_[p]), Transcendental ℚ e ∧
      ∀ i, r i^2 = RadicalLinearization.values (t : ℚ_[p]) ((κ : ℚ_[p])⁻¹) e i := by
  let f (i : Fin 4) (u : ℚ_[p]) := values (t : ℚ_[p]) (κ : ℚ_[p]) ((κ : ℚ_[p])⁻¹) u i
  obtain ⟨u,htrans,hr⟩ := transcendental_simultaneous_roots hp f 0 (constantValues T K)
    (fun i => by fin_cases i <;> dsimp only [f,values] <;> fun_prop)
    (fun i => by fin_cases i <;> simp [f,values,constantValues,← hT,← hK]) hu hs
  choose r hne hr using hr
  have hu0 : u ≠ 0 := by intro h; apply htrans; rw [h]; exact isAlgebraic_zero
  have hk : (κ : ℚ_[p]) ≠ 0 := by exact_mod_cast hκ
  exact ⟨(κ : ℚ_[p])/u^2,recovered u r,
    TranscendentalParameters.inverse_square htrans κ hκ,
    recovered_squares _ _ _ hk hu0 r hr⟩

end FourCorner.InfinityHenselRealization
#print axioms FourCorner.InfinityHenselRealization.recovered_squares
#print axioms FourCorner.InfinityHenselRealization.realize
