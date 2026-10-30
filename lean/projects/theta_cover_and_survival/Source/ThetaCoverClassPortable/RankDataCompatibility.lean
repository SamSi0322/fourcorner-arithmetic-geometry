import ThetaCoverClassPortable.ThetaStdSchemeFlatRank
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FourCorner.ThetaSurvivingActualJacobians.RankCompatibility
/-- Exact mathematical body of the original private ThetaStdSchemeFlatRank affine helper. -/
def originalAffineRank {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  f.appTop.hom.finrank (S.isoSpec.hom s)
/-- Exact mathematical body of the original public Scheme.Hom.finrank, using the
preceding exact original affine helper. Source byte comparisons pin both bodies. -/
def originalRank {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : ℕ :=
  originalAffineRank (pullback.snd f (S.affineOpenCover.f <| S.affineOpenCover.idx s))
    (S.affineOpenCover.covers s).choose
/-- A kernel checked typed equality for the only changed public data definition.
No private-name normalization is used in this proof. -/
theorem canonical_finrank_eq_original_code {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    f.finrank s=originalRank f s := rfl
/-- Exact original RingHom.finrank body; its raw Expr differs only in hygienic binder labels. -/
def originalRingRank {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : PrimeSpectrum R) : ℕ :=
  letI : Algebra R S := f.toAlgebra
  Module.rankAtStalk S x
theorem canonical_ring_finrank_eq_original_code {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : PrimeSpectrum R) : f.finrank x=originalRingRank f x := rfl
end FourCorner.ThetaSurvivingActualJacobians.RankCompatibility
