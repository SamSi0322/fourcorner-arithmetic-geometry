import CommonTower
import OddQuadraticParity
import geometry.PlaceTower

noncomputable section
set_option maxHeartbeats 1000000
namespace FourCorner.OddFourTower
open AlgebraicCurve CommonTower
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [NeZero (2 : K)]

theorem index_formula (w : Place K E) (a b c d : F) (r s u v : E)
    (hr : r^2 = algebraMap F E a) (hs : s^2 = algebraMap F E b)
    (hu : u^2 = algebraMap F E c) (hv : v^2 = algebraMap F E d)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hgen : Algebra.adjoin F {r,s,u,v} = ⊤) :
    w.ramificationIndex F =
      if Even ((w.restrict F).ord a) ∧ Even ((w.restrict F).ord b) ∧
          Even ((w.restrict F).ord c) ∧ Even ((w.restrict F).ord d)
      then 1 else 2 := by
  classical
  let A := first F E r
  let B := second F E r s
  let C := third F E r s u
  letI : IsScalarTower K A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional A B := FiniteDimensional.right F A B
  letI : FiniteDimensional B C := FiniteDimensional.right F B C
  letI : FiniteDimensional A C := FiniteDimensional.right F A C
  have h1r : r1 F E r ^ 2 = algebraMap F A a := by apply Subtype.ext; exact hr
  have h2r : r2 F E r s ^ 2 = algebraMap A B (algebraMap F A b) := by
    apply Subtype.ext; exact hs
  have h3r : r3 F E r s u ^ 2 = algebraMap B C (algebraMap F B c) := by
    apply Subtype.ext; exact hu
  have h4r : v^2 = algebraMap C E (algebraMap F C d) := by
    simpa only [← IsScalarTower.algebraMap_apply] using hv
  have h2F : (2:F) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K F)).mpr (NeZero.ne (2:K))
  have h2A : (2:A) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F A)).mpr h2F
  have h2B : (2:B) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F B)).mpr h2F
  have h2C : (2:C) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F C)).mpr h2F
  letI : Algebra.IsSeparable F A := RadicalSeparable.primitive h1r (gen1 F E r) h2F
  letI : Algebra.IsSeparable A B := RadicalSeparable.primitive h2r (gen2 F E r s) h2A
  letI : Algebra.IsSeparable B C := RadicalSeparable.primitive h3r (gen3 F E r s u) h2B
  letI : Algebra.IsSeparable C E := RadicalSeparable.primitive h4r (gen4 F E r s u v hgen) h2C
  have h1 := OddQuadraticParity.index_formula (w.restrict A) h1r (gen1 F E r) ha
    (finrank_le_two F A h1r (gen1 F E r))
  have h2 := OddQuadraticParity.index_formula (w.restrict B) h2r (gen2 F E r s)
    ((map_ne_zero (algebraMap F A)).mpr hb)
    (finrank_le_two A B h2r (gen2 F E r s))
  have h3 := OddQuadraticParity.index_formula (w.restrict C) h3r (gen3 F E r s u)
    ((map_ne_zero (algebraMap F B)).mpr hc)
    (finrank_le_two B C h3r (gen3 F E r s u))
  have h4 := OddQuadraticParity.index_formula w h4r (gen4 F E r s u v hgen)
    ((map_ne_zero (algebraMap F C)).mpr hd)
    (finrank_le_two C E h4r (gen4 F E r s u v hgen))
  simp only [PlaceTower.restrict_restrict] at h1 h2 h3 h4
  rw [Place.ord_restrict] at h2 h3 h4
  simp only [PlaceTower.restrict_restrict] at h2 h3 h4
  have hAB := PlaceTower.ramificationIndex_mul (K:=K) (F:=F) (E:=A) (L:=B) (w.restrict B)
  have hABC := PlaceTower.ramificationIndex_mul (K:=K) (F:=F) (E:=B) (L:=C) (w.restrict C)
  have hABCD := PlaceTower.ramificationIndex_mul (K:=K) (F:=F) (E:=C) (L:=E) w
  simp only [PlaceTower.restrict_restrict] at hAB hABC hABCD
  have hAB' : (w.restrict B).ramificationIndex F =
      if Even ((w.restrict F).ord a) ∧ Even ((w.restrict F).ord b) then 1 else 2 := by
    rw [hAB,h2,h1]
    simpa only [Nat.cast_ite,Nat.cast_one,Nat.cast_ofNat,Nat.mul_comm] using
      CommonQuadraticParity.parity_accumulate (Even ((w.restrict F).ord a)) ((w.restrict F).ord b)
  have hABC' : (w.restrict C).ramificationIndex F =
      if (Even ((w.restrict F).ord a) ∧ Even ((w.restrict F).ord b)) ∧
          Even ((w.restrict F).ord c) then 1 else 2 := by
    rw [hABC,h3,hAB']
    simpa only [Nat.cast_ite,Nat.cast_one,Nat.cast_ofNat,Nat.mul_comm] using
      CommonQuadraticParity.parity_accumulate
        (Even ((w.restrict F).ord a) ∧ Even ((w.restrict F).ord b)) ((w.restrict F).ord c)
  rw [hABCD,h4,hABC']
  have hh := CommonQuadraticParity.parity_accumulate
    ((Even ((w.restrict F).ord a) ∧ Even ((w.restrict F).ord b)) ∧ Even ((w.restrict F).ord c))
    ((w.restrict F).ord d)
  simpa only [Nat.cast_ite,Nat.cast_one,Nat.cast_ofNat,and_assoc,Nat.mul_comm] using hh

#print axioms index_formula
end FourCorner.OddFourTower
