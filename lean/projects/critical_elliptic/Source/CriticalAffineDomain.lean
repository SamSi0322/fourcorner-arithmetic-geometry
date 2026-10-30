import CriticalAffineTower

noncomputable section
namespace FourCorner.CriticalAffineDomain
open Polynomial CriticalSquareclasses CriticalAffineGeometry CriticalAffineTower
variable {k : Type*} [Field k]
set_option backward.isDefEq.respectTransparency.types false

/-- Injectivity is witnessed in the genuine rational biquadratic field. -/
theorem tower_coeff_injective (i : k) : Function.Injective (algebraMap k[X] (tower i)) := by
  intro p q hpq
  have h := congrArg (Biquadratic.CoordinateAlgebra.map k[X] (RatFunc k) (qB i) (qC i)) hpq
  rw [Biquadratic.CoordinateAlgebra.map_algebraMap,Biquadratic.CoordinateAlgebra.map_algebraMap] at h
  apply IsFractionRing.injective k[X] (RatFunc k)
  exact (algebraMap (RatFunc k) _).injective h

lemma toTower_aeval (i : k) (p : k[X]) :
    toTower i (Polynomial.aeval (coordinate i 0) p)=algebraMap k[X] (tower i) p := by
  rw [←toAffine_coeff]
  exact DFunLike.congr_fun (tower_inverse i) (algebraMap k[X] (tower i) p)

theorem aeval_injective (i : k) : Function.Injective (Polynomial.aeval (coordinate i 0) : k[X] →ₐ[k] ring i) := by
  intro p q hpq
  apply tower_coeff_injective i
  simpa only [toTower_aeval] using congrArg (toTower i) hpq

/-- The ORIGINAL V1/V0 coordinate is genuinely transcendental, independently
of any asserted curve/field isomorphism. -/
theorem coordinate_transcendental (i : k) : Transcendental k (coordinate i 0) :=
  transcendental_iff_injective.mpr (aeval_injective i)

/-- The literal V0 affine quotient is an actual domain, proved by its explicit
monic-tower isomorphism and the actual independent two-root field embedding. -/
theorem ring_isDomain (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) : IsDomain (ring i) := by
  have h2R : (2:RatFunc k)≠0 := by
    simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k (RatFunc k))).mpr h2
  letI : IsDomain (tower i) := Biquadratic.CoordinateAlgebra.coordinateRing_isDomain
    k[X] (RatFunc k) (qB i) (qC i) (IsFractionRing.injective _ _) h2R (independent i hi h2)
  exact Function.Injective.isDomain (equiv i).toRingHom (equiv i).injective
end FourCorner.CriticalAffineDomain
#print axioms FourCorner.CriticalAffineDomain.tower_coeff_injective
#print axioms FourCorner.CriticalAffineDomain.coordinate_transcendental
#print axioms FourCorner.CriticalAffineDomain.ring_isDomain
