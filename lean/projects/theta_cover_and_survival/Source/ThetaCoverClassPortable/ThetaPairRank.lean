import ThetaCoverClassPortable.ThetaPairDescent
import ThetaCoverClassPortable.ThetaStdRingFlatRank
noncomputable section
namespace FourCorner.ThetaPairRank
open Algebra AlgebraicGeometry
open scoped TensorProduct
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : ThetaPairPresentation.Data R S)
def unitBasis [Nontrivial R] (hb : IsUnit P.b) : Module.Basis (Fin 2) R S :=
  (ThetaQuadraticKernel.basisTwo P.b).map (ThetaPairPresentation.equiv P hb).symm.toLinearEquiv
lemma baseChange_finrank {W : Type u} [CommRing W] [Nontrivial W] [Algebra R W]
    (h : IsUnit (algebraMap R W P.a) ∨ IsUnit (algebraMap R W P.b)) :
    Module.finrank W (W ⊗[R] S)=2 := by
  rcases h with ha|hb
  · let b:=unitBasis (ThetaPairBaseChange.data (W:=W) (ThetaPairDescent.swap P)) ha
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  · let b:=unitBasis (ThetaPairBaseChange.data (W:=W) P) hb
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
/-- The rank at every genuine prime of the base is two. -/
theorem rankAtStalk (ell : R) (h : P.a+ell*P.b=1) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R:=R) S p=2 := by
  rw [Module.rankAtStalk_eq_finrank_tensorProduct]
  apply baseChange_finrank P
  have hn : P.a∉p.asIdeal ∨ P.b∉p.asIdeal := by
    by_contra hh
    push_neg at hh
    have h1 : (1:R)∈p.asIdeal := by
      rw [←h]
      exact p.asIdeal.add_mem hh.1 (p.asIdeal.mul_mem_left _ hh.2)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  rcases hn with ha|hb
  · exact Or.inl (IsLocalization.map_units (Localization.AtPrime p.asIdeal) (⟨P.a,ha⟩ : p.asIdeal.primeCompl))
  · exact Or.inr (IsLocalization.map_units (Localization.AtPrime p.asIdeal) (⟨P.b,hb⟩ : p.asIdeal.primeCompl))
end FourCorner.ThetaPairRank
#print axioms FourCorner.ThetaPairRank.rankAtStalk
