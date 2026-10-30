import ThetaCoverClassPortable.Slot03HighAdjacentAffineComparison
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

noncomputable section
namespace FourCorner.MonicBoundaryRegular
open Polynomial
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A regular base coordinate stays a non-zero-divisor in any flat algebra. -/
theorem algebraMap_isRegular [Module.Flat R S] {r : R} (hr : IsRegular r) :
    IsRegular (algebraMap R S r) := by
  have h := Module.Flat.isSMulRegular_of_isRegular (M := S) hr
  have h' : Function.Injective (fun x : S => algebraMap R S r * x) := by
    intro x y hxy
    apply h
    simpa only [Algebra.smul_def] using hxy
  exact ⟨h', fun x y hxy => h' (by simpa only [mul_comm] using hxy)⟩

/-- Localizing away from a regular coordinate loses no component or nilpotent. -/
theorem away_injective {r : S} (hr : IsRegular r) :
    Function.Injective (algebraMap S (Localization.Away r)) := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers r)
  rintro _ ⟨n,rfl⟩
  exact IsRegular.pow n hr

/-- A flat finite-chart algebra is a domain once its actual coordinate localization is. -/
theorem isDomain_of_flat_localization [Module.Flat R S] (r : R) (hr : IsRegular r)
    [IsDomain (Localization.Away (algebraMap R S r))] : IsDomain S :=
  Function.Injective.isDomain (algebraMap S (Localization.Away (algebraMap R S r)))
    (away_injective (algebraMap_isRegular hr))

/-- The generic dependent three-stage monic quadratic chart used at projective infinity. -/
abbrev First (a : R) := Multiquadratic.CoordinateAlgebra.Stage₁ R a
abbrev Tower (a : R) (b d : First a) := Biquadratic.CoordinateAlgebra.CoordinateRing (First a) b d

instance tower_free (a : R) (b d : First a) : Module.Free R (Tower a b d) :=
  Module.Free.trans (S := First a)

theorem tower_coordinate_regular (a : R) (b d : First a) (r : R) (hr : IsRegular r) :
    IsRegular (algebraMap R (Tower a b d) r) := algebraMap_isRegular hr

theorem tower_away_injective (a : R) (b d : First a) (r : R) (hr : IsRegular r) :
    Function.Injective (algebraMap (Tower a b d)
      (Localization.Away (algebraMap R (Tower a b d) r))) :=
  away_injective (tower_coordinate_regular a b d r hr)

#print axioms algebraMap_isRegular
#print axioms away_injective
#print axioms isDomain_of_flat_localization
#print axioms tower_coordinate_regular
#print axioms tower_away_injective
end FourCorner.MonicBoundaryRegular
