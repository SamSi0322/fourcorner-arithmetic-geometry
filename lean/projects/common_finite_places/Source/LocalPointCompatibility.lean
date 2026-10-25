import Genus17ActualLift
import Genus17TwistsPositive
import Mathlib.NumberTheory.Padics.PadicNumbers

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.LocalPointCompatibility
open Genus17Geometry
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

/-- A fixed actual rational point specializes to a point on the SAME Q-scheme
over each characteristic-zero field by an actual composition of Spec maps. -/
def pointOver (K : Type) [Field K] [CharZero K] {C : Scheme}
    (q : Spec (.of ℚ) ⟶ C) : Spec (.of K) ⟶ C :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) ≫ q

theorem pointOver_cover (K : Type) [Field K] [CharZero K] {C D : Scheme}
    (q : Spec (.of ℚ) ⟶ C) (p : Spec (.of ℚ) ⟶ D) (f : C ⟶ D) (h : q ≫ f = p) :
    pointOver K q ≫ f = pointOver K p := by
  simp only [pointOver,Category.assoc,h]

theorem pointOver_overQ (K : Type) [Field K] [CharZero K] {C : Scheme}
    (c : C ⟶ Spec (.of ℚ)) (q : Spec (.of ℚ) ⟶ C) :
    pointOver K q ≫ c = Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

def badPrimeCondition (t : ℚ) (p : ℕ) : Prop :=
  p ≤ 1153 ∨ padicValRat p t ≠ 0 ∨ padicValRat p (t-1) ≠ 0 ∨ padicValRat p (t+1) ≠ 0

def padicPoint (C : Scheme) (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  Nonempty (Spec (.of ℚ_[p]) ⟶ C)

/-- The actual everywhere-locally soluble twist set in the proposition. -/
def everywhereTwists (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : Finset ℚ :=
  (Genus17Support.twists t).filter fun κ =>
    Nonempty (Spec (.of ℝ) ⟶ curve t κ h0 h1 hm) ∧
      ∀ (p : ℕ) (hp : p.Prime), padicPoint (curve t κ h0 h1 hm) p hp

/-- The proposed finite test set, expressed on those same actual curves.
Its equivalence with everywhereTwists still requires the good-prime theorem. -/
def finiteTestTwists (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : Finset ℚ :=
  (Genus17Support.twists t).filter fun κ =>
    Nonempty (Spec (.of ℝ) ⟶ curve t κ h0 h1 hm) ∧
      ∀ (p : ℕ) (hp : p.Prime), badPrimeCondition t p → padicPoint (curve t κ h0 h1 hm) p hp

theorem everywhere_subset_finite (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    everywhereTwists t h0 h1 hm ⊆ finiteTestTwists t h0 h1 hm := by
  intro κ hκ
  obtain ⟨hκ,hr,hp⟩ := Finset.mem_filter.mp hκ
  exact Finset.mem_filter.mpr ⟨hκ,hr,fun p hprime _ => hp p hprime⟩

/-- One global point chooses ONE global kappa, and its actual rational lift
gives points on that same curve simultaneously at the real and every prime place. -/
theorem global_point_gives_everywhere_twist (t : ℚ) (ht : 1 < t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (p : Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t h0 h1 hm) :
    ∃ κ ∈ everywhereTwists t h0 h1 hm,
      ∃ q : Spec (.of ℚ) ⟶ curve t κ h0 h1 hm, q ≫ cover t κ h0 h1 hm = p := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra t
  obtain ⟨κ,hκ,hκpos,hdata⟩ := Genus17ActualLift.actual_point_lifts t ht h0 h1 hm p
  letI := Genus17Geometry.modelFieldAlgebra t κ
  obtain ⟨q,hq,hroot,hcoords⟩ := hdata
  refine ⟨κ,?_,q,hq⟩
  apply Finset.mem_filter.mpr
  refine ⟨hκ,⟨pointOver ℝ q⟩,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨pointOver ℚ_[p] q⟩

/-- The final implication of prop:common-finite-places on the actual complete D_t. -/
theorem everywhere_empty_no_rational_point (t : ℚ) (ht : 1 < t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (hempty : everywhereTwists t h0 h1 hm = ∅) :
    IsEmpty (Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t h0 h1 hm) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨κ,hκ,q,hq⟩ := global_point_gives_everywhere_twist t ht h0 h1 hm p
  simpa only [hempty,Finset.notMem_empty] using hκ

/-- Even the emptiness of the proposed finite tests already excludes actual
rational points; the converse local-set equivalence is not assumed here. -/
theorem finite_tests_empty_no_rational_point (t : ℚ) (ht : 1 < t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (hempty : finiteTestTwists t h0 h1 hm = ∅) :
    IsEmpty (Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t h0 h1 hm) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨κ,hκ,q,hq⟩ := global_point_gives_everywhere_twist t ht h0 h1 hm p
  have hh := everywhere_subset_finite t h0 h1 hm hκ
  simpa only [hempty,Finset.notMem_empty] using hh

end FourCorner.LocalPointCompatibility
#print axioms FourCorner.LocalPointCompatibility.pointOver_cover
#print axioms FourCorner.LocalPointCompatibility.global_point_gives_everywhere_twist
#print axioms FourCorner.LocalPointCompatibility.everywhere_empty_no_rational_point
#print axioms FourCorner.LocalPointCompatibility.finite_tests_empty_no_rational_point
