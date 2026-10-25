import ActualSourceCoset
import ActualSurvivingOrders
import CSFoundation.CommonSourceBeta

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit

/-- The literal rational source and its actual H/two-torsion decomposition.
This stores actual curve points and both ordered source squares. -/
structure ActualPair (n : ℤ) (hn : n ≠ 0) where
  a : ℚ
  b : ℚ
  c : ℚ
  e : ℚ
  u : ℚ
  v : ℚ
  hnpos : 0 < (n:ℚ)
  han : -(n:ℚ) < a
  ha : a < 0
  hc : (n:ℚ) < c
  hQ : CongruentEquation (n:ℚ) a b
  hR : CongruentEquation (n:ℚ) c e
  hu : u^2= -(a*c)/n
  hv : v^2= -((a-n)*(c-n))/n
  U : H n hn
  V : H n hn
  tauQ : Point (n:ℚ)
  tauR : Point (n:ℚ)
  htQ : 2 • tauQ=0
  htR : 2 • tauR=0
  hQU : finitePoint (by exact_mod_cast hn) hQ=(U:Point (n:ℚ))+tauQ
  hRV : finitePoint (by exact_mod_cast hn) hR=(V:Point (n:ℚ))+tauR
  hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation

namespace ActualPair
variable {n : ℤ} {hn : n ≠ 0} (S : ActualPair n hn)
lemma a_ne : S.a ≠ 0 := ne_of_lt S.ha
lemma c_ne : S.c ≠ 0 := ne_of_gt (lt_trans S.hnpos S.hc)
lemma am_ne : S.a-(n:ℚ) ≠ 0 := ne_of_lt (by linarith [S.ha,S.hnpos])
lemma ap_ne : S.a+(n:ℚ) ≠ 0 := ne_of_gt (by linarith [S.han])
lemma cm_ne : S.c-(n:ℚ) ≠ 0 := ne_of_gt (by linarith [S.hc])
lemma cp_ne : S.c+(n:ℚ) ≠ 0 := ne_of_gt (by linarith [S.hc,S.hnpos])
lemma e_ne : S.e ≠ 0 := by
  intro h
  have he := S.hR
  have hp : S.c*(S.c-(n:ℚ))*(S.c+(n:ℚ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero S.c_ne S.cm_ne) S.cp_ne
  apply hp
  simpa [CongruentEquation,h] using he.symm

/-- Coordinates of the two SAME H remainders, with no finite-point premise. -/
structure Remainders where
  x : ℚ
  y : ℚ
  w : ℚ
  z : ℚ
  hU : CongruentEquation (n:ℚ) x y
  hV : CongruentEquation (n:ℚ) w z
  eqU : (S.U:Point (n:ℚ))=finitePoint (by exact_mod_cast hn) hU
  eqV : (S.V:Point (n:ℚ))=finitePoint (by exact_mod_cast hn) hV

theorem remainders_nonempty : Nonempty S.Remainders := by
  obtain ⟨x,y,hU,hPU,_⟩ := source_remainder_coordinates hn S.hQ S.a_ne S.am_ne S.ap_ne
    S.U S.tauQ S.U.property S.htQ S.hQU
  obtain ⟨w,z,hV,hPV,_⟩ := source_remainder_coordinates hn S.hR S.c_ne S.cm_ne S.cp_ne
    S.V S.tauR S.V.property S.htR S.hRV
  exact ⟨⟨x,y,w,z,hU,hV,hPU,hPV⟩⟩

def remainders : S.Remainders := Classical.choice S.remainders_nonempty

namespace Remainders
variable {S} (r : S.Remainders)
theorem memU : finitePoint (by exact_mod_cast hn) r.hU ∈ H n hn := by
  rw [← r.eqU];exact S.U.property
theorem memV : finitePoint (by exact_mod_cast hn) r.hV ∈ H n hn := by
  rw [← r.eqV];exact S.V.property

theorem x_ne : r.x ≠ 0 := (actual_H_coordinate_data hn r.hU r.memU).1
theorem w_ne : r.w ≠ 0 := (actual_H_coordinate_data hn r.hV r.memV).1

theorem surviving_orders (hn8 : n%8=1 ∨ n%8=7) :
    (n%8=1 ∧ ((S.a=commonSourceTranslateMinus (n:ℚ) r.x ∧ S.c=commonSourceTranslatePlus (n:ℚ) r.w) ∨
      (S.a=commonSourceTranslatePlus (n:ℚ) r.x ∧ S.c=commonSourceTranslateMinus (n:ℚ) r.w))) ∨
    (n%8=7 ∧ ((S.a=r.x ∧ S.c=r.w) ∨
      (S.a=commonSourceTranslateZero (n:ℚ) r.x ∧ S.c=commonSourceTranslateZero (n:ℚ) r.w))) := by
  have hQU : finitePoint (by exact_mod_cast hn) S.hQ=finitePoint (by exact_mod_cast hn) r.hU+S.tauQ := by
    simpa only [r.eqU] using S.hQU
  have hRV : finitePoint (by exact_mod_cast hn) S.hR=finitePoint (by exact_mod_cast hn) r.hV+S.tauR := by
    simpa only [r.eqV] using S.hRV
  exact actual_source_surviving_orders hn hn8 S.hQ S.hR r.hU r.hV
    S.a_ne S.c_ne S.am_ne S.cm_ne S.ap_ne S.cp_ne S.hu S.hv r.memU r.memV
    S.tauQ S.tauR S.htQ S.htR hQU hRV S.hf
end Remainders

/-- The distinguished row is specified by the same global n-residue case. -/
def DistinguishedRow (W : H n hn) : Prop :=
    (n%8=1 → kummerDelta (n:ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd (W:Point (n:ℚ))) 0=
      scalarClass (n:ℚ) (by exact_mod_cast hn) ∧
      kummerDelta (n:ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd (W:Point (n:ℚ))) 1=1) ∧
    (n%8=7 → kummerDelta (n:ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd (W:Point (n:ℚ))) 0=
      scalarClass (-(n:ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn)) ∧
      kummerDelta (n:ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd (W:Point (n:ℚ))) 1=
      scalarClass (-(n:ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn)))

theorem complete_coset (hn8 : n%8=1 ∨ n%8=7)
    (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    (W : H n hn) (hW : DistinguishedRow W) :
    ∃ Z : H n hn, S.U+S.V=W+2 • Z := by
  have hpoint : ∃ Z ∈ H n hn, (S.U:Point (n:ℚ))+(S.V:Point (n:ℚ))=(W:Point (n:ℚ))+2 • Z := by
    rcases hn8 with h | h
    · exact actual_source_coset_one hn h S.hQ S.hR S.a_ne S.c_ne S.am_ne S.cm_ne S.ap_ne S.cp_ne
        S.hu S.hv hcompl S.U S.V W S.tauQ S.tauR S.U.property S.V.property
        S.hQU S.hRV S.htQ S.htR (hW.1 h).1 (hW.1 h).2
    · exact actual_source_coset_seven hn h S.hQ S.hR S.a_ne S.c_ne S.am_ne S.cm_ne S.ap_ne S.cp_ne
        S.hu S.hv hcompl S.U S.V W S.tauQ S.tauR S.U.property S.V.property
        S.hQU S.hRV S.htQ S.htR (hW.2 h).1 (hW.2 h).2
  obtain ⟨Z,hZ,hEq⟩ := hpoint
  exact ⟨⟨Z,hZ⟩,Subtype.ext hEq⟩

end ActualPair

/-- The only four possible labels, with the full compensating 2*phi(Z), force
both source labels to have the same parity. -/
theorem labels_same_parity_from_complete_coset {G : Type*} [AddCommGroup G]
    (phi : G →+ ZMod 4) (U V W Z : G) (hcoset : U+V=W+2 • Z)
    (hW : phi W=0 ∨ phi W=2) :
    ((phi U=0 ∨ phi U=2) ∧ (phi V=0 ∨ phi V=2)) ∨
    ((phi U=1 ∨ phi U=3) ∧ (phi V=1 ∨ phi V=3)) := by
  have he : phi U+phi V=phi W+2 • phi Z := by rw [← map_add,hcoset,map_add,map_nsmul]
  have finite_labels : ∀ u v w z : ZMod 4, u+v=w+2 • z → (w=0 ∨ w=2) →
      ((u=0 ∨ u=2) ∧ (v=0 ∨ v=2)) ∨ ((u=1 ∨ u=3) ∧ (v=1 ∨ v=3)) := by decide
  exact finite_labels _ _ _ _ he hW

#print axioms ActualPair.remainders_nonempty
#print axioms ActualPair.Remainders.surviving_orders
#print axioms ActualPair.complete_coset
#print axioms labels_same_parity_from_complete_coset
end FourCorner.CommonSource
