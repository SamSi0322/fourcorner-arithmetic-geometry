import FourCorner.PureSourceConverse
import FourCorner.FermatSymmetry

namespace FourCorner

@[ext]
theorem PurePoint.ext {a b : PurePoint}
    (hp : a.p = b.p) (hβ : a.β = b.β) (hU : a.U = b.U)
    (hV : a.V = b.V) (hW : a.W = b.W) (hT : a.T = b.T) : a = b := by
  cases a
  cases b
  simp_all

@[ext]
theorem ChamberPoint.ext {a b : ChamberPoint}
    (hx : a.x = b.x) (hy : a.y = b.y) (h0 : a.r₀ = b.r₀)
    (h1 : a.r₁ = b.r₁) (h2 : a.r₂ = b.r₂) (h3 : a.r₃ = b.r₃) : a = b := by
  cases a
  cases b
  simp_all

/-- Return to the strict square, preserving all four positive ordered roots. -/
def PurePoint.toChamber (a : PurePoint) : ChamberPoint where
  x := pureX a.U a.V a.W a.T
  y := pureY a.U a.V a.W a.T
  r₀ := pureR0 a.U a.T
  r₁ := pureR1 a.V a.W a.T
  r₂ := pureR2 a.V a.W a.T
  r₃ := pureR3 a.U a.T
  h := a.h.strictPoint.1
  hsum := a.h.strictPoint.2.1
  hdiff := a.h.strictPoint.2.2

/-- The chamber determines the pure parameters without an auxiliary choice. -/
def ChamberPoint.toPure (a : ChamberPoint) : PurePoint where
  p := radiusPureP a.r₀ a.r₁ a.r₂ a.r₃
  β := radiusPureBeta a.r₀ a.r₁ a.r₂ a.r₃
  U := radiusPureU a.r₀ a.r₃
  V := radiusPureV a.r₀ a.r₁ a.r₂ a.r₃
  W := radiusPureW a.r₀ a.r₁ a.r₂ a.r₃
  T := radiusPureT a.r₀ a.r₃
  h := strictPoint_pureCoordinates a.h a.hsum a.hdiff

theorem PurePoint.toChamber_toPure (a : PurePoint) : a.toChamber.toPure = a := by
  obtain ⟨hp,hβ,hU,hV,hW,hT⟩ := a.h.recover_parameters
  exact PurePoint.ext hp hβ hU hV hW hT

theorem ChamberPoint.toPure_toChamber (a : ChamberPoint) : a.toPure.toChamber = a := by
  have hd : a.r₀ - a.r₃ ≠ 0 :=
    ne_of_gt (strict_point_diagonal_bounds a.h a.hsum a.hdiff).1
  obtain ⟨h0,h1,h2,h3⟩ := radiusPure_recover_radii (r₁ := a.r₁) (r₂ := a.r₂) hd
  obtain ⟨hx,hy⟩ := radiusPure_recover_coordinates a.h.2.2.2.2.2.2.2.2 hd
  exact ChamberPoint.ext hx hy h0 h1 h2 h3

/-- A complete bijection between pure simultaneous-square data and strict chamber points. -/
def pureChamberEquiv : PurePoint ≃ ChamberPoint where
  toFun := PurePoint.toChamber
  invFun := ChamberPoint.toPure
  left_inv := PurePoint.toChamber_toPure
  right_inv := ChamberPoint.toPure_toChamber

/-- Central rotation preserves the strict model and its exact corner permutation. -/
theorem strictPoint_centralRotation {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    StrictPoint (1-x) (1-y) r₃ r₂ r₁ r₀ := by
  rcases h with ⟨hx₀,hx₁,hy₀,hy₁,h0,h1,h2,h3,hs0,hs1,hs2,hs3⟩
  refine ⟨by linarith, by linarith, by linarith, by linarith,
    h3,h2,h1,h0,?_,?_,?_,?_⟩
  all_goals nlinarith

/-- An upper-half strict point can be placed in the chosen chamber by exchange. -/
theorem strictPoint_upperHalf_chamber {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) (hs : 1 < x+y) : Nonempty ChamberPoint := by
  rcases lt_or_gt_of_ne (strict_point_not_diagonal h) with hlt | hgt
  · exact ⟨⟨y,x,r₀,r₂,r₁,r₃,strict_point_exchange h, by linarith, hlt⟩⟩
  · exact ⟨⟨x,y,r₀,r₁,r₂,r₃,h,hs,hgt⟩⟩

/-- Every original strict point admits a chamber representative under square symmetries. -/
theorem strictPoint_chamber_exists {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : Nonempty ChamberPoint := by
  rcases lt_or_gt_of_ne (strict_point_not_antidiagonal h) with hlt | hgt
  · exact strictPoint_upperHalf_chamber (strictPoint_centralRotation h) (by linarith)
  · exact strictPoint_upperHalf_chamber h hgt

/-- The pure model is nonempty exactly when the original strict four-corner problem has a point. -/
theorem originalStrictPoint_iff_purePoint :
    (∃ x y r₀ r₁ r₂ r₃ : ℚ, StrictPoint x y r₀ r₁ r₂ r₃) ↔ Nonempty PurePoint := by
  constructor
  · rintro ⟨x,y,r₀,r₁,r₂,r₃,h⟩
    obtain ⟨c⟩ := strictPoint_chamber_exists h
    exact ⟨pureChamberEquiv.symm c⟩
  · rintro ⟨p⟩
    let c := pureChamberEquiv p
    exact ⟨c.x,c.y,c.r₀,c.r₁,c.r₂,c.r₃,c.h⟩

#print axioms originalStrictPoint_iff_purePoint
#print axioms PurePoint.toChamber_toPure
#print axioms ChamberPoint.toPure_toChamber
#print axioms pureChamberEquiv
end FourCorner
