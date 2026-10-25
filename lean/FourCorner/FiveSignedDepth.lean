import FourCorner.DenominatorBoundsArithmetic
import FourCorner.FiveNormalizeAux

set_option autoImplicit false
namespace FourCorner
namespace IntegralModel

/-- Once the four actual radii have common 5-adic order `s`, dividing them
by `5^s` reduces their square differences by `5^(2*s)`. The odd-prime
factorization therefore gives an actual signed sum of depth `2*h - 3*s`. -/
theorem five_signed_value (M : IntegralModel) (s : ℕ)
    (h0 : padicValInt 5 M.A₀ = s) (h1 : padicValInt 5 M.A₁ = s)
    (h2 : padicValInt 5 M.A₂ = s) (h3 : padicValInt 5 M.A₃ = s)
    (hXY : ¬ (5 : ℤ) ∣ M.X * M.Y) (hdeep : 2*s < padicValInt 5 M.L) :
    ∃ b c d : ℤ, (b = M.A₁ ∨ b = -M.A₁) ∧
      (c = M.A₂ ∨ c = -M.A₂) ∧ (d = M.A₃ ∨ d = -M.A₃) ∧
      M.A₀-b-c+d ≠ 0 ∧
      padicValInt 5 (M.A₀-b-c+d) = 2*padicValInt 5 M.L-3*s := by
  have hp : Nat.Prime 5 := Nat.prime_five
  let : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨a, ha, han, hva⟩ := FiveNormalizeAux.normalize M.A₀ s
    (ne_of_gt M.A₀_pos) (by omega)
  obtain ⟨b, hb, hbn, hvb⟩ := FiveNormalizeAux.normalize M.A₁ s
    (ne_of_gt M.A₁_pos) (by omega)
  obtain ⟨c, hc, hcn, hvc⟩ := FiveNormalizeAux.normalize M.A₂ s
    (ne_of_gt M.A₂_pos) (by omega)
  obtain ⟨d, hd, hdn, hvd⟩ := FiveNormalizeAux.normalize M.A₃ s
    (ne_of_gt M.A₃_pos) (by omega)
  obtain ⟨N, hN, hNn, hvN⟩ := FiveNormalizeAux.normalize M.L (2*s)
    (ne_of_gt M.L_pos) (by omega)
  let q : ℤ := 5^s
  have hqn : q ≠ 0 := by dsimp [q]; positivity
  have hq2n : q^2 ≠ 0 := pow_ne_zero 2 hqn
  have hNL : M.L = q^2*N := by
    simpa only [q, ← pow_mul, Nat.mul_comm s 2] using hN
  have haunit : ¬ (5:ℤ) ∣ a := by
    intro hpdiv
    have := BoundsValuation.padic_pos_of_dvd hp han hpdiv
    omega
  have hpN : (5:ℤ) ∣ N := by
    have he : 1 ≤ padicValInt 5 N := by omega
    simpa using (padicValInt_dvd_iff (p:=5) 1 N).mpr (Or.inr he)
  have hpL : (5:ℤ) ∣ M.L := by
    rw [hNL]
    exact dvd_mul_of_dvd_right hpN _
  have hpX : ¬ (5:ℤ) ∣ M.X := fun h => hXY (dvd_mul_of_dvd_left h _)
  have hpY : ¬ (5:ℤ) ∣ M.Y := fun h => hXY (dvd_mul_of_dvd_right h _)
  have hdxunit : ¬ (5:ℤ) ∣ M.L-2*M.X := by omega
  have hdyunit : ¬ (5:ℤ) ∣ M.L-2*M.Y := by omega
  have hdxn : M.L-2*M.X ≠ 0 := by
    intro hz
    exact hdxunit (by simp [hz])
  have hdyn : M.L-2*M.Y ≠ 0 := by
    intro hz
    exact hdyunit (by simp [hz])
  have hflag : a^2+d^2=b^2+c^2 := by
    apply mul_left_cancel₀ hq2n
    calc
      q^2*(a^2+d^2) = M.A₀^2+M.A₃^2 := by rw [ha,hd]; dsimp [q]; ring
      _ = M.A₁^2+M.A₂^2 := M.bounds_flag
      _ = q^2*(b^2+c^2) := by rw [hb,hc]; dsimp [q]; ring
  have hB : b^2-a^2=N*(M.L-2*M.X) := by
    apply mul_left_cancel₀ hq2n
    calc
      q^2*(b^2-a^2) = M.A₁^2-M.A₀^2 := by rw [ha,hb]; dsimp [q]; ring
      _ = M.L*(M.L-2*M.X) := M.bounds_horizontal_difference
      _ = q^2*(N*(M.L-2*M.X)) := by rw [hNL]; ring
  have hC : c^2-a^2=N*(M.L-2*M.Y) := by
    apply mul_left_cancel₀ hq2n
    calc
      q^2*(c^2-a^2) = M.A₂^2-M.A₀^2 := by rw [ha,hc]; dsimp [q]; ring
      _ = M.L*(M.L-2*M.Y) := M.bounds_vertical_difference
      _ = q^2*(N*(M.L-2*M.Y)) := by rw [hNL]; ring
  have hD : d^2-a^2=N*(2*(M.L-M.X-M.Y)) := by
    apply mul_left_cancel₀ hq2n
    calc
      q^2*(d^2-a^2) = M.A₃^2-M.A₀^2 := by rw [ha,hd]; dsimp [q]; ring
      _ = M.L*(2*(M.L-M.X-M.Y)) := M.bounds_diagonal_difference
      _ = q^2*(N*(2*(M.L-M.X-M.Y))) := by rw [hNL]; ring
  obtain ⟨b',c',d',hb',hc',hd',_,_,_,htn,hvt⟩ :=
    BoundsValuation.odd_value_from_differences hp (by decide)
      a b c d N (M.L-2*M.X) (M.L-2*M.Y) (2*(M.L-M.X-M.Y))
      hNn hdxn hdyn hpN haunit hflag hB hC hD
  have hraw : M.A₀-q*b'-q*c'+q*d' = q*(a-b'-c'+d') := by
    rw [ha]; dsimp [q]; ring
  refine ⟨q*b',q*c',q*d',?_,?_,?_,?_,?_⟩
  · rcases hb' with rfl|rfl
    · exact Or.inl hb.symm
    · right; rw [hb]; dsimp [q]; ring
  · rcases hc' with rfl|rfl
    · exact Or.inl hc.symm
    · right; rw [hc]; dsimp [q]; ring
  · rcases hd' with rfl|rfl
    · exact Or.inl hd.symm
    · right; rw [hd]; dsimp [q]; ring
  · rw [hraw]
    exact mul_ne_zero hqn htn
  · rw [hraw, padicValInt.mul hqn htn]
    have hvq : padicValInt 5 q = s := by
      dsimp [q]
      rw [padicValInt, Int.natAbs_pow]
      exact padicValNat.prime_pow (p := 5) s
    rw [hvq]
    rw [padicValInt.eq_zero_of_not_dvd hdxunit,
      padicValInt.eq_zero_of_not_dvd hdyunit] at hvt
    omega

private theorem sign_of_choice {A b : ℤ} (hb : b=A ∨ b= -A) :
    ∃ e : ℤ, (e=1 ∨ e= -1) ∧ b=e*A := by
  rcases hb with rfl|rfl
  · exact ⟨1, Or.inl rfl, by ring⟩
  · exact ⟨-1, Or.inr rfl, by ring⟩

/-- Explicit `±1` coefficients on the four original, unnormalized radii. -/
theorem five_signed_sum_depth (M : IntegralModel) (s : ℕ)
    (h0 : padicValInt 5 M.A₀ = s) (h1 : padicValInt 5 M.A₁ = s)
    (h2 : padicValInt 5 M.A₂ = s) (h3 : padicValInt 5 M.A₃ = s)
    (hXY : ¬ (5 : ℤ) ∣ M.X * M.Y) (hdeep : 2*s < padicValInt 5 M.L) :
    ∃ e₀ e₁ e₂ e₃ : ℤ,
      (e₀=1 ∨ e₀= -1) ∧ (e₁=1 ∨ e₁= -1) ∧
      (e₂=1 ∨ e₂= -1) ∧ (e₃=1 ∨ e₃= -1) ∧
      e₀*M.A₀+e₁*M.A₁+e₂*M.A₂+e₃*M.A₃ ≠ 0 ∧
      padicValInt 5 (e₀*M.A₀+e₁*M.A₁+e₂*M.A₂+e₃*M.A₃) =
        2*padicValInt 5 M.L-3*s := by
  obtain ⟨b,c,d,hb,hc,hd,hn,hv⟩ := M.five_signed_value s h0 h1 h2 h3 hXY hdeep
  obtain ⟨eb,heb,rfl⟩ := sign_of_choice hb
  obtain ⟨ec,hec,rfl⟩ := sign_of_choice hc
  obtain ⟨ed,hed,rfl⟩ := sign_of_choice hd
  refine ⟨1,-eb,-ec,ed,Or.inl rfl,?_,?_,hed,?_,?_⟩
  · rcases heb with rfl|rfl <;> simp
  · rcases hec with rfl|rfl <;> simp
  · convert hn using 1; ring
  · convert hv using 1; congr 1; ring

end IntegralModel
end FourCorner
#print axioms FourCorner.IntegralModel.five_signed_sum_depth
