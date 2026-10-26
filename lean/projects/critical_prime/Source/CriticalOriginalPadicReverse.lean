import CriticalPadicReverse
import CrtSupport.CriticalBasicLiftWave24

noncomputable section
namespace FourCorner.CriticalPadicConverse
open CriticalNormalizedRadii
variable {p : ℕ} [Fact p.Prime]

/-- The exact ordered integer distance polynomials, cast to Qp, supply the
four original completed-field equations without changing any root label. -/
lemma equations_of_original (X Y L : ℤ) (A : Fin 4 → ℚ_[p])
    (hroot : ∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p])) : Equations X Y L A := by
  have h0:=hroot 0
  have h1:=hroot 1
  have h2:=hroot 2
  have h3:=hroot 3
  simp only [criticalRadicands,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons,Int.cast_add,Int.cast_sub,Int.cast_pow] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

/-- Single-local-point reverse with the paper's literal criticalRadicands.
The depth is unrestricted and the roots are the given SAME actual Qp tuple. -/
theorem original_padic_roots_to_unit_pattern (hodd : p≠2) (X Y L : ℤ) (s : ℕ) (hs : 1≤s)
    (A : Fin 4 → ℚ_[p])
    (hprim : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1)
    (hL : padicValInt p L=2*s)
    (hroot : ∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ)) :
    UnitCriticalSquarePattern p :=
  unit_pattern_of_padic_roots hodd X Y L s hs A hprim
    (equations_of_original X Y L A (fun j=>(hroot j).1)) hL (fun j=>(hroot j).2)

/-- Natural primitive coordinates, exactly as the existing forward all-depth
construction: actual completed-field roots give the original unit pattern. -/
theorem nat_padic_roots_to_unit_pattern (hodd : p≠2) (X Y L s : ℕ) (hs : 1≤s)
    (A : Fin 4 → ℚ_[p]) (hprim : Nat.gcd (Nat.gcd X Y) L=1)
    (hL : padicValNat p L=2*s)
    (hroot : ∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ)) :
    UnitCriticalSquarePattern p := by
  apply original_padic_roots_to_unit_pattern hodd X Y L s hs A
  · simpa only [Int.natAbs_natCast] using hprim
  · simpa only [padicValInt,Int.natAbs_natCast] using hL
  · exact hroot

/-- Even one actual strict primitive local point at a positive depth excludes
5 and13. Interior inequalities are retained in this literal paper wrapper. -/
theorem strict_nat_local_reverse (hodd : p≠2) (X Y L s : ℕ) (hs : 1≤s)
    (hX : 0<X) (hY : 0<Y) (hXL : X<L) (hYL : Y<L)
    (A : Fin 4 → ℚ_[p]) (hprim : Nat.gcd (Nat.gcd X Y) L=1)
    (hL : padicValNat p L=2*s)
    (hroot : ∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ)) :
    UnitCriticalSquarePattern p ∧ p≠5 ∧ p≠13 := by
  have hpat:=nat_padic_roots_to_unit_pattern hodd X Y L s hs A hprim hL hroot
  exact ⟨hpat,critical_pattern_excludes_exceptional (unitCriticalSquarePattern_to_pattern hpat)⟩

/-- The (iii)->(ii)/(i) direction requires only the weaker existence-at-each-
depth consequence of the paper's infinitely-many-triples clause. -/
theorem all_depths_local_reverse (hodd : p≠2)
    (hlocal : ∀ s : ℕ,1≤s→∃ X Y L : ℕ,0<X ∧ 0<Y ∧ X<L ∧ Y<L ∧
      Nat.gcd (Nat.gcd X Y) L=1 ∧ padicValNat p L=2*s ∧
      ∃ A : Fin 4 → ℚ_[p],∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ)) :
    UnitCriticalSquarePattern p ∧ p≠5 ∧ p≠13 := by
  obtain ⟨X,Y,L,hX,hY,hXL,hYL,hprim,hL,A,hA⟩:=hlocal 1 le_rfl
  exact strict_nat_local_reverse hodd X Y L 1 le_rfl hX hY hXL hYL A hprim hL hA
end FourCorner.CriticalPadicConverse
#print axioms FourCorner.CriticalPadicConverse.original_padic_roots_to_unit_pattern
#print axioms FourCorner.CriticalPadicConverse.nat_padic_roots_to_unit_pattern
#print axioms FourCorner.CriticalPadicConverse.strict_nat_local_reverse
#print axioms FourCorner.CriticalPadicConverse.all_depths_local_reverse
