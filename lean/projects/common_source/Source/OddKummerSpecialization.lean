import ActualSourceDepth
import Slot14.OddProbe
import CSFoundation.CommonSourceOddLocal

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit

variable (q : ℕ) [Fact q.Prime]

/-- The canonical map on ordered signed square classes at the specified prime. -/
def squareClassToPadic : Units.modPow ℚ 2 →* Units.modPow ℚ_[q] 2 :=
  Units.modPow.map (Rat.castHom ℚ_[q]).toMonoidHom 2

@[simp] theorem squareClassToPadic_scalar (a : ℚ) (ha : a ≠ 0) :
    squareClassToPadic q (scalarClass a ha) =
      scalarClass (a : ℚ_[q]) (by exact_mod_cast ha) := by
  unfold squareClassToPadic scalarClass
  rw [Units.modPow.map_mk]
  apply congrArg QuotientGroup.mk
  apply Units.ext
  rfl

/-- Specializing the actual first ordered Kummer slot proves local squareness
of the abscissa. No local point or local square class is chosen independently. -/
theorem first_slot_local_square {n x y d : ℚ} (hn : n ≠ 0)
    (hP : CongruentEquation n x y) (hx : x ≠ 0) (hxm : x-n ≠ 0) (hxp : x+n ≠ 0)
    (hd : d ≠ 0)
    (hclass : kummerDelta n hn (Multiplicative.ofAdd (finitePoint hn hP)) 0 = scalarClass d hd)
    (hs : IsSquare (d:ℚ_[q])) : IsSquare (x:ℚ_[q]) := by
  rw [kummerDelta_finitePoint hn hP hx hxm hxp] at hclass
  have hlocal := congrArg (squareClassToPadic q) hclass
  change squareClassToPadic q (scalarClass x hx)=squareClassToPadic q (scalarClass d hd) at hlocal
  rw [squareClassToPadic_scalar,squareClassToPadic_scalar] at hlocal
  apply (scalarClass_eq_one_iff _ _).mp
  exact hlocal.trans ((scalarClass_eq_one_iff _ _).mpr hs)

/-- Every actual H point with locally square distinguished first slot has
square finite-reduction abscissa. Infinity is handled before extracting
coordinates; no hypothesis about sample generators replaces the actual point. -/
theorem H_first_slot_reduction_square {n : ℤ} (hn : n ≠ 0)
    (hq2 : q ≠ 2) (hnq : (n:ZMod q) ≠ 0) (P : H n hn)
    (d : ℚ) (hd : d ≠ 0)
    (hclass : kummerDelta (n:ℚ) (by exact_mod_cast hn)
      (Multiplicative.ofAdd (P:Point (n:ℚ))) 0=scalarClass d hd)
    (hs : IsSquare (d:ℚ_[q])) (a b : ZMod q)
    (hred : residueCoordinates (reduce n hq2 hnq (P:Point (n:ℚ)))=some (a,b)) :
    IsSquare a := by
  rcases P with ⟨P,hPH⟩
  cases P with
  | zero =>
    change residueCoordinates (reduce n hq2 hnq (0:Point (n:ℚ)))=some (a,b) at hred
    rw [map_zero] at hred
    cases hred
  | some x y he =>
    have hE := (congruentEquation_iff_weierstrass (n:ℚ) x y).mpr he.left
    have hpH : finitePoint (by exact_mod_cast hn) hE ∈ H n hn := hPH
    obtain ⟨hx,hxm,hxp,_⟩ := actual_H_coordinate_data hn hE hpH
    have hlocal := first_slot_local_square q (by exact_mod_cast hn) hE hx hxm hxp hd hclass hs
    by_contra hns
    exact Slot14.nonsquare_abscissa_of_reduction hq2 hnq hE hred hns hlocal

/-- Both distinguished global first slots in the manuscript specialize to
squares at a permitted odd probe. -/
theorem distinguished_local_first_slots {n : ℤ} (hq : q%8=5)
    (hns : IsSquare (n:ℚ_[q])) :
    IsSquare (n:ℚ_[q]) ∧ IsSquare (-(n:ℚ_[q])) := by
  refine ⟨hns,?_⟩
  simpa using (csOdd_isSquare_neg_one hq).mul hns

#print axioms first_slot_local_square
#print axioms H_first_slot_reduction_square
#print axioms distinguished_local_first_slots
end FourCorner.CommonSource
