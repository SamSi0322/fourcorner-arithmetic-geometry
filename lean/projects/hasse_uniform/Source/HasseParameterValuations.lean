import HasseFiniteAssembly

namespace FourCorner.HasseParameterValuations

open HilbertArithmeticHigh11 HasseInertParity

theorem positive_p_neighbors_zero (q : OddPrime) (p : ℚ) (hp : 1<p)
    (hv : 0<padicValRat q.val p) :
    padicValRat q.val (p-1)=0 ∧ padicValRat q.val (p+1)=0 := by
  have hm : padicValRat q.val (-1 : ℚ)=0 := by rw [padicValRat.neg,padicValRat.one]
  have hma := padicValRat.add_eq_of_lt (p:=q.val) (q:=-1) (r:=p)
    (by linarith) (by norm_num) (by linarith)
    (by rw [hm];exact hv)
  have hpa := padicValRat.add_eq_of_lt (p:=q.val) (q:=1) (r:=p)
    (by linarith) one_ne_zero (by linarith)
    (by rw [padicValRat.one];exact hv)
  constructor
  · have he : -1+p=p-1 := by ring
    simpa only [he,hm] using hma
  · have he : 1+p=p+1 := by ring
    simpa only [he,padicValRat.one] using hpa

theorem pole_neighbors_equal (q : OddPrime) (p : ℚ) (hp : 1<p)
    (hv : padicValRat q.val p<0) :
    padicValRat q.val (p-1)=padicValRat q.val p ∧
      padicValRat q.val (p+1)=padicValRat q.val p := by
  have hm : padicValRat q.val (-1 : ℚ)=0 := by rw [padicValRat.neg,padicValRat.one]
  have hma := padicValRat.add_eq_of_lt (p:=q.val) (q:=p) (r:=-1)
    (by linarith) (by linarith) (by norm_num)
    (by rw [hm];exact hv)
  have hpa := padicValRat.add_eq_of_lt (p:=q.val) (q:=p) (r:=1)
    (by linarith) (by linarith) one_ne_zero (by rw [padicValRat.one];exact hv)
  constructor
  · simpa only [sub_eq_add_neg] using hma
  · exact hpa

theorem positive_a_p_zero (q : OddPrime) (p : ℚ) (hp : 1<p)
    (hv : 0<padicValRat q.val (p-1)) : padicValRat q.val p=0 := by
  have he : 1+(p-1)=p := by ring
  have hh := padicValRat.add_eq_of_lt (p:=q.val) (q:=1) (r:=p-1)
    (by rw [he];linarith) one_ne_zero (by linarith) (by rw [padicValRat.one];exact hv)
  simpa only [he,padicValRat.one] using hh

theorem positive_b_neighbors_zero (q : OddPrime) (p : ℚ) (hp : 1<p)
    (hv : 0<padicValRat q.val (p+1)) :
    padicValRat q.val p=0 ∧ padicValRat q.val (p-1)=0 := by
  have hm : padicValRat q.val (-1 : ℚ)=0 := by rw [padicValRat.neg,padicValRat.one]
  have htwo : padicValRat q.val (-2 : ℚ)=0 := by rw [padicValRat.neg,val_two q]
  have he : -1+(p+1)=p := by ring
  have hh := padicValRat.add_eq_of_lt (p:=q.val) (q:=-1) (r:=p+1)
    (by rw [he];linarith) (by norm_num) (by linarith) (by rw [hm];exact hv)
  have he2 : -2+(p+1)=p-1 := by ring
  have hh2 := padicValRat.add_eq_of_lt (p:=q.val) (q:=-2) (r:=p+1)
    (by rw [he2];linarith) (by norm_num) (by linarith) (by rw [htwo];exact hv)
  exact ⟨by simpa only [he,hm] using hh,by simpa only [he2,htwo] using hh2⟩

/-- Complete odd-prime valuation partition for p,p−1,p+1. -/
theorem all_odd_branches (q : OddPrime) (p : ℚ) (hp : 1<p) :
    (padicValRat q.val p=0 ∧ padicValRat q.val (p-1)=0 ∧ padicValRat q.val (p+1)=0) ∨
    0<padicValRat q.val p ∨ 0<padicValRat q.val (p-1) ∨ 0<padicValRat q.val (p+1) ∨
    (padicValRat q.val p<0 ∧ Even (padicValRat q.val p)) ∨
    (padicValRat q.val p<0 ∧ Odd (padicValRat q.val p)) := by
  rcases lt_trichotomy (padicValRat q.val p) 0 with hn | hz | hpos
  · rcases Int.even_or_odd (padicValRat q.val p) with he | ho
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hn,he⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hn,ho⟩))))
  · have ha := padicValRat.min_le_padicValRat_add (p:=q.val) (q:=p) (r:=-1)
      (by linarith)
    have hb := padicValRat.min_le_padicValRat_add (p:=q.val) (q:=p) (r:=1) (by linarith)
    have he : p+ -1=p-1 := by ring
    rw [he,hz,padicValRat.neg,padicValRat.one,min_self] at ha
    rw [hz,padicValRat.one,min_self] at hb
    by_cases hapos : 0<padicValRat q.val (p-1)
    · exact Or.inr (Or.inr (Or.inl hapos))
    by_cases hbpos : 0<padicValRat q.val (p+1)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hbpos)))
    · exact Or.inl ⟨hz,by omega,by omega⟩
  · exact Or.inr (Or.inl hpos)

#print axioms all_odd_branches
#print axioms pole_neighbors_equal

end FourCorner.HasseParameterValuations
