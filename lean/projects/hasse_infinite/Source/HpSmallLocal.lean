import HpSmallResidue
import HpFamilyResidue

namespace FourCorner.HpSmallLocal
open HpResidueCharts HpSmallResidue
noncomputable section
theorem seven_ne : (1 : ZMod 7) ≠ 3 := by decide
theorem eleven_ne : (9 : ZMod 11) ≠ 5 := by decide
variable {q : ℕ} [Fact q.Prime]

theorem prime_list (hq : q ≠ 2) (hlt : q<101) :
    q=3 ∨ q=5 ∨ q=7 ∨ q=11 ∨ q=13 ∨ q=17 ∨ q=19 ∨ q=23 ∨ q=29 ∨ q=31 ∨ q=37 ∨ q=41 ∨ q=43 ∨ q=47 ∨ q=53 ∨ q=59 ∨ q=61 ∨ q=67 ∨ q=71 ∨ q=73 ∨ q=79 ∨ q=83 ∨ q=89 ∨ q=97 := by
  have h : ∀n : Fin 101,n.val.Prime → n.val ≠ 2 →
      n.val=3 ∨ n.val=5 ∨ n.val=7 ∨ n.val=11 ∨ n.val=13 ∨ n.val=17 ∨ n.val=19 ∨ n.val=23 ∨ n.val=29 ∨ n.val=31 ∨ n.val=37 ∨ n.val=41 ∨ n.val=43 ∨ n.val=47 ∨ n.val=53 ∨ n.val=59 ∨ n.val=61 ∨ n.val=67 ∨ n.val=71 ∨ n.val=73 ∨ n.val=79 ∨ n.val=83 ∨ n.val=89 ∨ n.val=97 := by decide
  exact h ⟨q,hlt⟩ Fact.out hq

theorem residue_charts (hq : q ≠ 2) (hlt : q<101) (p : ZMod q)
    (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hr : IsSquare (2*(p+1))) (hs : IsSquare (3-p))
    (h7 : q=7 → p ≠ 3) (h11 : q=11 → p ≠ 5) : Charts p := by
  rcases prime_list hq hlt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact charts3 p hp ha hb hr hs h7 h11
  · exact charts5 p hp ha hb hr hs h7 h11
  · exact charts7 p hp ha hb hr hs h7 h11
  · exact charts11 p hp ha hb hr hs h7 h11
  · exact charts13 p hp ha hb hr hs h7 h11
  · exact charts17 p hp ha hb hr hs h7 h11
  · exact charts19 p hp ha hb hr hs h7 h11
  · exact charts23 p hp ha hb hr hs h7 h11
  · exact charts29 p hp ha hb hr hs h7 h11
  · exact charts31 p hp ha hb hr hs h7 h11
  · exact charts37 p hp ha hb hr hs h7 h11
  · exact charts41 p hp ha hb hr hs h7 h11
  · exact charts43 p hp ha hb hr hs h7 h11
  · exact charts47 p hp ha hb hr hs h7 h11
  · exact charts53 p hp ha hb hr hs h7 h11
  · exact charts59 p hp ha hb hr hs h7 h11
  · exact charts61 p hp ha hb hr hs h7 h11
  · exact charts67 p hp ha hb hr hs h7 h11
  · exact charts71 p hp ha hb hr hs h7 h11
  · exact charts73 p hp ha hb hr hs h7 h11
  · exact charts79 p hp ha hb hr hs h7 h11
  · exact charts83 p hp ha hb hr hs h7 h11
  · exact charts89 p hp ha hb hr hs h7 h11
  · exact charts97 p hp ha hb hr hs h7 h11

/-- Complete small-prime residue check for the exact family, followed by
the exhaustive finite/branch/infinity actual Hensel realizations. -/
theorem family_small_good (hq : q ≠ 2) (hlt : q<101) (j : ℕ) (P : ℤ_[q])
    (hP : (P : ℚ_[q])=(HpInfiniteArithmetic.p j : ℚ_[q]))
    (hP0 : PadicInt.toZMod P ≠ 0) (hPa : PadicInt.toZMod P-1 ≠ 0)
    (hPb : PadicInt.toZMod P+1 ≠ 0) :
    ∃S : HasseNorms.LocalPoint ℚ_[q] (HpInfiniteArithmetic.p j : ℚ_[q]),Transcendental ℚ S.rho := by
  obtain ⟨hr,hs⟩ := HpFamilyResidue.conic_squares j P hP
  have h7 : q=7 → PadicInt.toZMod P ≠ 3 := by
    intro h
    subst q
    rw [HpFamilyResidue.residue_seven j P hP]
    exact seven_ne
  have h11 : q=11 → PadicInt.toZMod P ≠ 5 := by
    intro h
    subst q
    rw [HpFamilyResidue.residue_eleven j P hP]
    exact eleven_ne
  exact HpGoodLocal.charts_lift hq _ (HpInfiniteArithmetic.p_gt_one j) P hP hP0 hPa hPb
    (residue_charts hq hlt _ hP0 hPa hPb hr hs h7 h11)

#print axioms prime_list
#print axioms residue_charts
#print axioms family_small_good
end
end FourCorner.HpSmallLocal
