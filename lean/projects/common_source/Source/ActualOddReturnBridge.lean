import ActualPairData
import ActualCyclicLabels
import OddWrongReturn
import OddEvenMismatch

noncomputable section
namespace FourCorner.CommonSource
variable {n : ℤ} {hn : n ≠ 0} {q : ℕ} [Fact q.Prime]

/-- The actual ordered rational source cannot have two odd cyclic remainders
at a wrong-unit probe. Rational coordinates are transported together. -/
theorem actual_pair_odd_remainders_impossible (S : ActualPair n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hq2 : q≠2) (hnq : (n:ZMod q) ≠ 0)
    (r : S.Remainders) (i : ZMod q) (hi : i^2= -1) (yu yv : ZMod q)
    (hredU : residueCoordinates (reduce n hq2 hnq S.U)=some ((n:ZMod q)*i,yu))
    (hredV : residueCoordinates (reduce n hq2 hnq S.V)=some ((n:ZMod q)*i,yv))
    (hwrong1 : n%8=1 → ¬ IsSquare ((1-i)/2))
    (hwrong7 : n%8=7 → ¬ IsSquare ((1+i)/2))
    (hfq : IsSquare (commonSourceReturn (n:ℚ_[q]) S.a S.c)) : False := by
  rw [r.eqU] at hredU
  rw [r.eqV] at hredV
  obtain ⟨hx,hxr,_⟩ := integral_coordinates_of_reduction_some hq2 hnq r.hU hredU
  obtain ⟨hw,hwr,_⟩ := integral_coordinates_of_reduction_some hq2 hnq r.hV hredV
  let N : ℤ_[q] := n
  let U := rationalIntegral q r.x hx
  let V := rationalIntegral q r.w hw
  have hnN : PadicInt.toZMod N ≠ 0 := by simpa [N] using hnq
  have hu : PadicInt.toZMod U=PadicInt.toZMod N*i := by simpa [U,N] using hxr
  have hv : PadicInt.toZMod V=PadicInt.toZMod N*i := by simpa [V,N] using hwr
  rcases r.surviving_orders hn8 with ⟨h1,ho⟩ | ⟨h7,ho⟩
  · have hloc : ((S.a:ℚ_[q])=commonSourceTranslateMinus (N:ℚ_[q]) U ∧
        (S.c:ℚ_[q])=commonSourceTranslatePlus (N:ℚ_[q]) V) ∨
        ((S.a:ℚ_[q])=commonSourceTranslatePlus (N:ℚ_[q]) U ∧
        (S.c:ℚ_[q])=commonSourceTranslateMinus (N:ℚ_[q]) V) := by
      dsimp [N,U,V,rationalIntegral,commonSourceTranslateMinus,commonSourceTranslatePlus] at ho ⊢
      exact_mod_cast ho
    exact odd_remainders_wrong_return_one N U V i hq2 hnN hi hu hv hloc (hwrong1 h1) hfq
  · have hloc : ((S.a:ℚ_[q])=(U:ℚ_[q]) ∧ (S.c:ℚ_[q])=(V:ℚ_[q])) ∨
        ((S.a:ℚ_[q])=commonSourceTranslateZero (N:ℚ_[q]) U ∧
        (S.c:ℚ_[q])=commonSourceTranslateZero (N:ℚ_[q]) V) := by
      dsimp [N,U,V,rationalIntegral,commonSourceTranslateZero] at ho ⊢
      exact_mod_cast ho
    exact odd_remainders_wrong_return_seven N U V i hq2 hnN hi hu hv hloc (hwrong7 h7) hfq

/-- All four same-source mismatched even-label cases are excluded, using the
actual reduction map and unbounded local disk arguments. -/
theorem actual_pair_even_mismatch_impossible (S : ActualPair n hn)
    (hn8 : n%8=1 ∨ n%8=7) (hq : q%8=5) (hnq : (n:ZMod q) ≠ 0)
    (hns : IsSquare (n:ℚ_[q])) (r : S.Remainders)
    (hu : reduce n (by omega:q≠2) hnq S.U=0 ∨ reduce n (by omega:q≠2) hnq S.U=residueT0 n hnq)
    (hv : reduce n (by omega:q≠2) hnq S.V=0 ∨ reduce n (by omega:q≠2) hnq S.V=residueT0 n hnq)
    (hne : reduce n (by omega:q≠2) hnq S.U ≠ reduce n (by omega:q≠2) hnq S.V)
    (hfq : IsSquare (commonSourceReturn (n:ℚ_[q]) S.a S.c)) : False := by
  rw [r.eqU] at hu hne
  rw [r.eqV] at hv hne
  have hmis := actual_even_reduction_mismatch (by omega:q≠2) hnq r.hU r.hV hu hv hne
  have hQ : (S.b:ℚ_[q])^2=(S.a:ℚ_[q])*(S.a-n)*(S.a+n) := by exact_mod_cast S.hQ
  have hR : (S.e:ℚ_[q])^2=(S.c:ℚ_[q])*(S.c-n)*(S.c+n) := by exact_mod_cast S.hR
  have he : (S.e:ℚ_[q]) ≠ 0 := by exact_mod_cast S.e_ne
  have hnorm := parameter_norm_eq_one n hnq
  rcases r.surviving_orders hn8 with ⟨h1,ho⟩ | ⟨h7,ho⟩
  · have hloc : ((S.a:ℚ_[q])=commonSourceTranslateMinus (n:ℚ_[q]) r.x ∧
        (S.c:ℚ_[q])=commonSourceTranslatePlus (n:ℚ_[q]) r.w) ∨
        ((S.a:ℚ_[q])=commonSourceTranslatePlus (n:ℚ_[q]) r.x ∧
        (S.c:ℚ_[q])=commonSourceTranslateMinus (n:ℚ_[q]) r.w) := by
      dsimp [commonSourceTranslateMinus,commonSourceTranslatePlus] at ho ⊢
      exact_mod_cast ho
    exact even_mismatch_wrong_return_one hq hnorm hns he hQ hR hmis hloc hfq
  · have hloc : ((S.a:ℚ_[q])=(r.x:ℚ_[q]) ∧ (S.c:ℚ_[q])=(r.w:ℚ_[q])) ∨
        ((S.a:ℚ_[q])=commonSourceTranslateZero (n:ℚ_[q]) r.x ∧
        (S.c:ℚ_[q])=commonSourceTranslateZero (n:ℚ_[q]) r.w) := by
      dsimp [commonSourceTranslateZero] at ho ⊢
      exact_mod_cast ho
    exact even_mismatch_wrong_return_seven hq hnorm hns (by exact_mod_cast r.x_ne)
      (by exact_mod_cast r.w_ne) he hQ hR hmis hloc hfq

#print axioms actual_pair_odd_remainders_impossible
#print axioms actual_pair_even_mismatch_impossible
end FourCorner.CommonSource
