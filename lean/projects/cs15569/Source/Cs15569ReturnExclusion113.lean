import Cs15569ActualSourceImage113

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

def FourPairs113 (a c : F113) : Prop :=
  (a=11 ∧ c=81) ∨ (a=16 ∧ c=87) ∨ (a=81 ∧ c=11) ∨ (a=87 ∧ c=16)

/-- A known finite abscissa is the residue of the SAME rational coordinate;
its actual reduction being finite proves integrality, rather than assuming it. -/
theorem integral_abscissa_of_red113 {x y : ℚ} (he : CongruentEquation 15569 x y)
    {a : F113} (ha : abscissa113 (red113 (finitePoint (by norm_num) he))=some a) :
    ∃ hx : (primeIdeal 113).valuation ℚ x≤1,
      PadicInt.toZMod (rationalIntegral 113 x hx)=a := by
  have hc := coordinates113_reduce (finitePoint (by norm_num) he)
  cases hred : red113 (finitePoint (by norm_num) he) with
  | zero => rw [hred] at ha; cases ha
  | some X Y hXY =>
    rw [hred] at ha hc
    have hXa : X=a := Option.some.inj ha
    have hcoords : residueCoordinates (reduce (q:=113) 15569 (by decide) (by decide)
        (finitePoint (by norm_num) he))=some (X,Y) := hc.symm
    obtain ⟨hx,hxr,_⟩ := integral_coordinates_of_reduction_some (q:=113) (by decide) (by decide) he hcoords
    exact ⟨hx,hxr.trans hXa⟩

private theorem finite_cross_product_nonsquare (a c : F113) (hrows : FourPairs113 a c) :
    ¬ IsSquare ((a+c)*(2*(c+15569))) := by
  have hd : (2*(c+15569) : F113) ≠ 0 := by
    rcases hrows with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  intro hs
  apply Cs15569Finite.four_pair_exclusion a c hrows
  have hh := hs.div (IsSquare.sq (2*(c+15569)))
  have heq : ((a+c)*(2*(c+15569)))/(2*(c+15569))^2=Cs15569Finite.returnResidue a c := by
    unfold Cs15569Finite.returnResidue
    field_simp
  exact heq ▸ hh

/-- Transfer from the actual integral coordinate pair to its literal return.
This covers every rational height and imposes no bound on a square root. -/
theorem integral_four_pair_return_nonsquare (a c : ℤ_[113])
    (hrows : FourPairs113 (PadicInt.toZMod a) (PadicInt.toZMod c)) :
    ¬ IsSquare (commonSourceReturn (15569 : ℚ_[113]) (a : ℚ_[113]) (c : ℚ_[113])) := by
  have hncast : ((15569 : ℤ_[113]) : ℚ_[113])=(15569 : ℚ_[113]) := by
    change (((15569 : ℕ) : ℤ_[113]) : ℚ_[113])=15569
    rw [PadicInt.coe_natCast]
    norm_num
  have h2cast : ((2 : ℤ_[113]) : ℚ_[113])=(2 : ℚ_[113]) := by
    change (((2 : ℕ) : ℤ_[113]) : ℚ_[113])=2
    rw [PadicInt.coe_natCast]
    norm_num
  have hres : ¬ IsSquare (PadicInt.toZMod ((a+c)*(2*(c+15569)))) := by
    simp only [map_mul,map_add,map_ofNat]
    exact finite_cross_product_nonsquare _ _ hrows
  have hbad := commonSource_ratio_nonsquare_of_residue (a+c) (2*(c+15569)) hres
  have hid : ((a+c : ℤ_[113]) : ℚ_[113])/((2*(c+15569) : ℤ_[113]) : ℚ_[113])=
      commonSourceReturn (15569 : ℚ_[113]) (a : ℚ_[113]) (c : ℚ_[113]) := by
    rw [PadicInt.coe_add,PadicInt.coe_mul,PadicInt.coe_add,h2cast,hncast]
    rfl
  rw [hid] at hbad
  exact hbad

/-- The literal original return at113 is excluded after the proven same-source
four-row image. No finite image hypothesis is supplied by the caller. -/
theorem actual_pair_exclusion (S : ActualPair 15569 n15569_ne_zero)
    (hs2 : IsSquare (commonSourceReturn (15569 : ℚ_[2]) S.a S.c))
    (hs3 : IsSquare (commonSourceReturn (15569 : ℚ_[3]) S.a S.c))
    (hs113 : IsSquare (commonSourceReturn (15569 : ℚ_[113]) S.a S.c)) : False := by
  let r := S.remainders
  have hrows := actual_source_four_abscissae S r hs2 hs3
  have hex : ∃ A C : F113, FourPairs113 A C ∧
      abscissa113 (red113 (finitePoint (by norm_num) S.hQ))=some A ∧
      abscissa113 (red113 (finitePoint (by norm_num) S.hR))=some C := by
    rcases hrows with h | h | h | h
    · exact ⟨11,81,Or.inl ⟨rfl,rfl⟩,(Prod.mk.inj h).1,(Prod.mk.inj h).2⟩
    · exact ⟨16,87,Or.inr (Or.inl ⟨rfl,rfl⟩),(Prod.mk.inj h).1,(Prod.mk.inj h).2⟩
    · exact ⟨81,11,Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)),(Prod.mk.inj h).1,(Prod.mk.inj h).2⟩
    · exact ⟨87,16,Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩)),(Prod.mk.inj h).1,(Prod.mk.inj h).2⟩
  obtain ⟨A,C,hrows,hA,hC⟩ := hex
  obtain ⟨ha,hra⟩ := integral_abscissa_of_red113 S.hQ hA
  obtain ⟨hc,hrc⟩ := integral_abscissa_of_red113 S.hR hC
  have hbad := integral_four_pair_return_nonsquare (rationalIntegral 113 S.a ha)
    (rationalIntegral 113 S.c hc) (by simpa only [hra,hrc] using hrows)
  exact hbad hs113

#print axioms integral_abscissa_of_red113
#print axioms integral_four_pair_return_nonsquare
#print axioms actual_pair_exclusion
end
end FourCorner.Cs15569Completion
