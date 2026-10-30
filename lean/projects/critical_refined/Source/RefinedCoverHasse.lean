import CriticalDoublePointCount
import CriticalRefinedNumerics

noncomputable section
namespace FourCorner.RefinedCoverHasse
open AlgebraicCurve
variable (k:Type*) [Field k]
set_option maxHeartbeats 2000000
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants k i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants k i).toModule

/-- Reuse the TWO proved actual-field isomorphisms. No isogeny count or
independent point-count assertion is a premise. -/
def coverBaseEquiv (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    CriticalLiteralDouble.field k i ≃ₐ[k] CriticalRadicalField.field k i :=
  (CriticalDoubleFieldIso.equiv k i hi h2).trans (CriticalOriginalFieldEquiv.equiv k i hi h2)

def degreeOneEquiv (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1} ≃
      {v:Place k (CriticalRadicalField.field k i) //v.deg=1} :=
  (Place.congrEquiv (coverBaseEquiv k i hi h2).toRingEquiv
    (coverBaseEquiv k i hi h2).commutes).subtypeEquiv
    (fun w=>by rw [Place.congrEquiv_apply,Place.deg_congrRingEquiv])

theorem hasse_bound [Finite k] (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    |(Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1}:ℝ)-
      ((Nat.card k:ℝ)+1)|≤2*Real.sqrt (Nat.card k:ℝ) := by
  have he:=Nat.card_congr (degreeOneEquiv k i hi h2)
  rw [he]
  exact (CriticalFiniteGenus.hasse_bound k i hi h2).2

theorem count_gt_fortyEight [Finite k] (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (hq:73≤Nat.card k) :
    48<Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1} :=
  CriticalRefinedNumerics.count_gt_fortyEight _ _ hq (hasse_bound k i hi h2)

theorem count_gt_sixteen [Finite k] (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (hq:29≤Nat.card k) :
    16<Nat.card {w:Place k (CriticalLiteralDouble.field k i) //w.deg=1} :=
  CriticalRefinedNumerics.count_gt_sixteen _ _ hq (hasse_bound k i hi h2)

#print axioms coverBaseEquiv
#print axioms hasse_bound
#print axioms count_gt_fortyEight
#print axioms count_gt_sixteen
end FourCorner.RefinedCoverHasse
