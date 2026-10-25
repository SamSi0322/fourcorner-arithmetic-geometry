import FourCorner.FermatSymmetry

set_option autoImplicit false
namespace FourCorner

/-- A point with its four original corner labels. No condition is built into
this data type; `strict` is precisely the original four-distance predicate. -/
structure LabelledSquareData where
  x : ℚ
  y : ℚ
  r₀ : ℚ
  r₁ : ℚ
  r₂ : ℚ
  r₃ : ℚ

namespace LabelledSquareData

def strict (d : LabelledSquareData) : Prop :=
  StrictPoint d.x d.y d.r₀ d.r₁ d.r₂ d.r₃

def inChamber (d : LabelledSquareData) : Prop := 1 < d.x+d.y ∧ d.y<d.x

end LabelledSquareData

/-- Four genuine square isometries suffice to select the chamber. -/
inductive ChamberMotion where
  | identity
  | exchange
  | halfTurn
  | halfTurnExchange
  deriving DecidableEq

namespace ChamberMotion

/-- The action transports the point and all four labelled radii together. -/
def act (g : ChamberMotion) (d : LabelledSquareData) : LabelledSquareData :=
  match g with
  | identity => d
  | exchange => ⟨d.y,d.x,d.r₀,d.r₂,d.r₁,d.r₃⟩
  | halfTurn => ⟨1-d.x,1-d.y,d.r₃,d.r₂,d.r₁,d.r₀⟩
  | halfTurnExchange => ⟨1-d.y,1-d.x,d.r₃,d.r₁,d.r₂,d.r₀⟩

/-- Each listed motion is an involution on the complete labelled datum. -/
theorem act_involutive (g : ChamberMotion) (d : LabelledSquareData) :
    g.act (g.act d) = d := by
  cases g <;> cases d <;> simp only [act]
  all_goals congr 1 <;> ring

/-- All four square identities, positivity of each radius, and every strict
coordinate inequality are preserved by each actual square symmetry. -/
theorem preserves_strict (g : ChamberMotion) {d : LabelledSquareData}
    (h : d.strict) : (g.act d).strict := by
  cases g
  · exact h
  · exact strict_point_exchange h
  · rcases h with ⟨hx0,hx1,hy0,hy1,h0,h1,h2,h3,hs0,hs1,hs2,hs3⟩
    change StrictPoint (1-d.x) (1-d.y) d.r₃ d.r₂ d.r₁ d.r₀
    refine ⟨by linarith,by linarith,by linarith,by linarith,h3,h2,h1,h0,?_,?_,?_,?_⟩
    all_goals nlinarith
  · rcases h with ⟨hx0,hx1,hy0,hy1,h0,h1,h2,h3,hs0,hs1,hs2,hs3⟩
    change StrictPoint (1-d.y) (1-d.x) d.r₃ d.r₁ d.r₂ d.r₀
    refine ⟨by linarith,by linarith,by linarith,by linarith,h3,h1,h2,h0,?_,?_,?_,?_⟩
    all_goals nlinarith

/-- The two diagonal coordinates acquire the two independent signs. -/
theorem diagonal_action (g : ChamberMotion) (d : LabelledSquareData) :
    ((g.act d).x+(g.act d).y-1,(g.act d).x-(g.act d).y) =
      match g with
      | identity => (d.x+d.y-1,d.x-d.y)
      | exchange => (d.x+d.y-1,-(d.x-d.y))
      | halfTurn => (-(d.x+d.y-1),-(d.x-d.y))
      | halfTurnExchange => (-(d.x+d.y-1),d.x-d.y) := by
  cases g <;> simp only [act] <;> apply Prod.ext <;> dsimp <;> ring

end ChamberMotion

/-- Select a chamber representative in the orbit of this very same labelled
strict point, using a displayed genuine square symmetry. -/
theorem strictPoint_chamber_motion {d : LabelledSquareData} (h : d.strict) :
    ∃ g : ChamberMotion, (g.act d).strict ∧ (g.act d).inChamber := by
  have hsne := strict_point_not_antidiagonal h
  have hdne := strict_point_not_diagonal h
  rcases lt_or_gt_of_ne hsne with hs | hs
  · rcases lt_or_gt_of_ne hdne with hd | hd
    · refine ⟨.halfTurn,ChamberMotion.preserves_strict .halfTurn h,?_,?_⟩
      all_goals dsimp [ChamberMotion.act]; linarith
    · refine ⟨.halfTurnExchange,ChamberMotion.preserves_strict .halfTurnExchange h,?_,?_⟩
      all_goals dsimp [ChamberMotion.act]; linarith
  · rcases lt_or_gt_of_ne hdne with hd | hd
    · refine ⟨.exchange,ChamberMotion.preserves_strict .exchange h,?_,?_⟩
      all_goals dsimp [ChamberMotion.act]; linarith
    · exact ⟨.identity,h,hs,hd⟩

/-- Manuscript lem:ell-diagonal-exclusion, including the orbit-certified
chamber construction rather than only the exclusion of the two diagonals. -/
theorem diagonal_exclusion_and_chamber {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    x ≠ y ∧ x+y ≠ 1 ∧
      ∃ g : ChamberMotion,
        let d := g.act ⟨x,y,r₀,r₁,r₂,r₃⟩
        StrictPoint d.x d.y d.r₀ d.r₁ d.r₂ d.r₃ ∧ 1 < d.x+d.y ∧ d.y<d.x := by
  refine ⟨strict_point_not_diagonal h,strict_point_not_antidiagonal h,?_⟩
  exact strictPoint_chamber_motion (d:=⟨x,y,r₀,r₁,r₂,r₃⟩) h

end FourCorner
#print axioms FourCorner.ChamberMotion.act_involutive
#print axioms FourCorner.ChamberMotion.preserves_strict
#print axioms FourCorner.ChamberMotion.diagonal_action
#print axioms FourCorner.strictPoint_chamber_motion
#print axioms FourCorner.diagonal_exclusion_and_chamber
