import HasseDyadicUnitOneRow

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
namespace FourCorner.HasseDyadicUnitFifteenFinite

def oddLift (x : ZMod 16) : ZMod 32 := 2*(x.val : ZMod 32)+1
def fourLift (s : ZMod 8) : ZMod 32 := 4*(s.val : ZMod 32)
def n (s x y z : ZMod 32) : ZMod 32 := x+y+2*z+s*((x+2*z)*(x+y)+2)
def r4 : ZMod 32 →+* ZMod 4 := ZMod.castHom (by decide) _
def r16 : ZMod 32 →+* ZMod 16 := ZMod.castHom (by decide) _

def signResidue (s : ZMod 32) (N : ZMod 16) : Prop :=
  if (s.val/4)%2=0 then (N=2 ∨ N=14) else (N=6 ∨ N=10)
instance (s : ZMod 32) (N : ZMod 16) : Decidable (signResidue s N) :=
  inferInstanceAs (Decidable (if (s.val/4)%2=0 then (N=2 ∨ N=14) else (N=6 ∨ N=10)))

private theorem finite_normalized : ∀ (S : ZMod 8) (X Y Z : ZMod 16),
    let s := fourLift S
    let x := oddLift X
    let y := oddLift Y
    let z := oddLift Z
    (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1) →
    (1-s^2)*y^2=1-2*s^2*z^2 →
    r4 (x+y)=0 → signResidue s (r16 (n s x y z)) := by decide

private theorem odd_lift_exists : ∀ x : ZMod 32, x.val%2=1 →
    ∃ X : ZMod 16, x=oddLift X := by decide

private theorem four_lift_exists : ∀ s : ZMod 32, r4 s=0 →
    ∃ S : ZMod 8, s=fourLift S := by decide

/-- The exact unit-fifteen numerator residue, on the literal mod-32 source
relations. The unrestricted S retains every valuation depth. -/
theorem numerator_residue (s x y z : ZMod 32)
    (hs : r4 s=0) (hxodd : x.val%2=1) (hyodd : y.val%2=1) (hzodd : z.val%2=1)
    (hx : (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1))
    (hy : (1-s^2)*y^2=1-2*s^2*z^2) (ho : r4 (x+y)=0) :
    signResidue s (r16 (n s x y z)) := by
  obtain ⟨S,rfl⟩ := four_lift_exists s hs
  obtain ⟨X,rfl⟩ := odd_lift_exists x hxodd
  obtain ⟨Y,rfl⟩ := odd_lift_exists y hyodd
  obtain ⟨Z,rfl⟩ := odd_lift_exists z hzodd
  exact finite_normalized S X Y Z hx hy ho

#print axioms numerator_residue
end FourCorner.HasseDyadicUnitFifteenFinite
