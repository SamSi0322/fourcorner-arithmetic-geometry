import RefinedProductSquares

noncomputable section
namespace FourCorner.CriticalRefinedCompletion
open CriticalRefinedWave27
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000

/-- The original local coordinate construction, now retaining the square
of EVERY prescribed signed coordinate as the normalized radicand residue. -/
theorem signed_local_radicand_data (hodd : p≠2) (s : ℕ) (hs : 1≤s)
    (i b : ZMod p) (V : Fin 4 → ZMod p)
    (hsp : SignedPattern i b (V 0) (V 1) (V 2) (V 3)) :
    ∃ X Y : ℤ, ∃ qs : Fin 4 → ℤ,
      ¬(p:ℤ)∣X ∧ ¬(p:ℤ)∣Y ∧
      (∀ j,criticalRadicands X Y ((p:ℤ)^(2*s)) j=(p:ℤ)^(2*s)*qs j) ∧
      ∀ j,(qs j:ZMod p)=(V j)^2 := by
  obtain ⟨hi,hb,h1,h2,h3⟩ := hsp
  obtain ⟨X,Y,q,hXu,hYu,hnorm,hq,hX,hY⟩ :=
    critical_local_coordinates hodd s hs i b ((V 0)^2) hi hb
  let N : ℤ :=(p:ℤ)^(2*s)
  let qs : Fin 4 → ℤ := ![q,q-2*X+N,q-2*Y+N,q-2*X-2*Y+2*N]
  have hN : (N:ZMod p)=0 := by
    dsimp [N]
    push_cast
    rw [ZMod.natCast_self]
    exact zero_pow (by omega)
  have hres : ∀ j : Fin 4,(qs j:ZMod p)=
      (![V 0^2,V 0^2+b,V 0^2+i*b,V 0^2+(1+i)*b] : Fin 4 → ZMod p) j := by
    intro j
    fin_cases j <;> simp [qs] <;> push_cast <;>
      simp only [hq,hN,mul_zero,add_zero] <;>
      first | linear_combination hX | linear_combination hY | linear_combination hX+hY
  refine ⟨X,Y,qs,hXu,hYu,?_,?_⟩
  · intro j
    fin_cases j <;> simp [criticalRadicands,qs] <;> dsimp [N] at * <;>
      linear_combination hnorm
  · intro j
    rw [hres j]
    fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three] <;> first | rfl | exact h1.symm | exact h2.symm | exact h3.symm

/-- Actual original radicands at congruent triples keep all prescribed
normalized residues, so later Hensel roots can retain all four desired signs. -/
theorem transport_signed_data (s : ℕ) (X Y L X' Y' L' : ℤ) (q : Fin 4 → ℤ)
    (V : Fin 4 → ZMod p)
    (hX : (p:ℤ)^(2*s+1)∣X'-X) (hY : (p:ℤ)^(2*s+1)∣Y'-Y)
    (hL : (p:ℤ)^(2*s+1)∣L'-L)
    (hfac : ∀ j,criticalRadicands X Y L j=(p:ℤ)^(2*s)*q j)
    (hres : ∀ j,(q j:ZMod p)=(V j)^2) :
    ∃ q' : Fin 4 → ℤ,(∀ j,criticalRadicands X' Y' L' j=(p:ℤ)^(2*s)*q' j) ∧
      ∀ j,(q' j:ZMod p)=(V j)^2 := by
  have hd := critical_radicands_congr ((p:ℤ)^(2*s+1)) X Y L X' Y' L' hX hY hL
  choose d hd using hd
  let q' : Fin 4 → ℤ := fun j=>q j+p*d j
  refine ⟨q',?_,?_⟩
  · intro j
    have hj:=hd j
    rw [hfac j,pow_succ] at hj
    dsimp [q']
    linear_combination hj
  · intro j
    simpa only [q',Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,
      zero_mul,add_zero] using hres j
end FourCorner.CriticalRefinedCompletion
#print axioms FourCorner.CriticalRefinedCompletion.signed_local_radicand_data
#print axioms FourCorner.CriticalRefinedCompletion.transport_signed_data
