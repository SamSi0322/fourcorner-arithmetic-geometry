import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Unramified.Field

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalCoverSchemeProperties
open CategoryTheory AlgebraicGeometry

/-- Finite-type formally unramified algebras have finite-dimensional actual
residue fibers, hence are quasi-finite. No field/perfectness condition on R. -/
theorem algebra_quasiFinite_of_formallyUnramified
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.FormallyUnramified R S] : Algebra.QuasiFinite R S := by
  constructor
  intro P hP
  letI : Algebra.FormallyUnramified P.ResidueField (P.Fiber S) := inferInstance
  letI : Algebra.FiniteType P.ResidueField (P.Fiber S) := inferInstance
  exact Algebra.FormallyUnramified.finite_of_free P.ResidueField (P.Fiber S)

/-- Native formally-unramified finite-type Scheme morphisms are locally
quasi-finite. This is a proved generic API bridge, not an actual-cover premise. -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [FormallyUnramified f] : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  let φ := (f.appLE U V e).hom
  have hft : φ.FiniteType := f.finiteType_appLE hU hV e
  have hfu : φ.FormallyUnramified := f.formallyUnramified_appLE hU hV e
  dsimp only [φ] at hft hfu
  algebraize [(f.appLE U V e).hom]
  change Algebra.QuasiFinite _ _
  exact algebra_quasiFinite_of_formallyUnramified

/-- Native all-stalk criterion, retaining every Scheme point (not only K-points). -/
theorem formallyUnramified_of_all_stalks {X Y : Scheme} (f : X ⟶ Y)
    (h : ∀ x : X, (f.stalkMap x).hom.FormallyUnramified) : FormallyUnramified f :=
  HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime h

/-- A proper morphism satisfying the actual all-point stalk criterion is
native finite and native formally unramified, with no normalization identity
or assumed finite morphism inserted. Properness supplies finite type. -/
theorem finite_and_formallyUnramified_of_all_stalks {X Y : Scheme} (f : X ⟶ Y)
    [IsProper f] (h : ∀ x : X, (f.stalkMap x).hom.FormallyUnramified) :
    IsFinite f ∧ FormallyUnramified f := by
  letI : FormallyUnramified f := formallyUnramified_of_all_stalks f h
  letI : LocallyQuasiFinite f := locallyQuasiFinite_of_formallyUnramified f
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite f,inferInstance⟩

#print axioms algebra_quasiFinite_of_formallyUnramified
#print axioms locallyQuasiFinite_of_formallyUnramified
#print axioms formallyUnramified_of_all_stalks
#print axioms finite_and_formallyUnramified_of_all_stalks
end FourCorner.CriticalCoverSchemeProperties
