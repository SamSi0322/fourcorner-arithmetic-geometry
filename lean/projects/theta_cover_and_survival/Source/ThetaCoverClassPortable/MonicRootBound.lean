import ThetaCoverClassPortable.EtaleSchemePointLocalHomeomorph
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Order.Lattice

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (A K : Type) [CommRing A] [Algebra ℚ A]
  [NontriviallyNormedField K] [Algebra ℚ K]

include A in
/-- Cauchy's bound for a fixed actual monic A-polynomial varies continuously with A(K). -/
theorem continuous_monic_cauchyBound (p : Polynomial A) (hp : p.Monic) :
    Continuous (fun φ : A →ₐ[ℚ] K => (p.map φ.toRingHom).cauchyBound) := by
  have hn (φ : A →ₐ[ℚ] K) : (p.map φ.toRingHom).natDegree=p.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (by simp [hp.leadingCoeff])
  simp only [Polynomial.cauchyBound,hn,(hp.map _).leadingCoeff,nnnorm_one,div_one,
    Polynomial.coeff_map]
  exact (Continuous.finset_sup_apply (s:=Finset.range p.natDegree)
    (fun i _ => (continuous_evaluation ℚ A K (p.coeff i)).nnnorm)).add continuous_const

variable (S : Type) [CommRing S] [Algebra A S] [Algebra ℚ S] [IsScalarTower ℚ A S]

/-- Every actual integral generator stays norm-bounded above a genuine open neighborhood
of any base point; the bound comes from its actual monic annihilating polynomial. -/
theorem integral_element_locally_bounded (s : S) (hs : IsIntegral A s) (φ₀ : A →ₐ[ℚ] K) :
    ∃ (U : Set (A →ₐ[ℚ] K)) (C : NNReal), IsOpen U ∧ φ₀∈U ∧
      ∀ f : S →ₐ[ℚ] K, f.comp (Algebra.algHom ℚ A S)∈U → ‖f s‖₊≤C := by
  obtain ⟨p,hp,hps⟩ := hs
  let bound : (A →ₐ[ℚ] K) → NNReal := fun φ => (p.map φ.toRingHom).cauchyBound
  let C : NNReal := bound φ₀+1
  let U := {φ : A →ₐ[ℚ] K | bound φ<C}
  have hb : Continuous bound := continuous_monic_cauchyBound A K p hp
  refine ⟨U,C,isOpen_lt hb continuous_const,?_,?_⟩
  · change bound φ₀<bound φ₀+1
    exact lt_add_one _
  · intro f hf
    let φ := f.comp (Algebra.algHom ℚ A S)
    have hcompat : (algebraMap K K).comp φ.toRingHom=f.toRingHom.comp (algebraMap A S) := rfl
    have hroot : (p.map φ.toRingHom).IsRoot (f s) := by
      have h := Polynomial.map_aeval_eq_aeval_map hcompat p s
      have hps' : Polynomial.aeval s p=0 := by simpa only [Polynomial.aeval_def] using hps
      rw [hps',map_zero] at h
      change 0=(p.map φ.toRingHom).eval (f s) at h
      exact h.symm
    exact (hroot.norm_lt_cauchyBound (hp.map _).ne_zero).le.trans (le_of_lt hf)

end FourCorner.ThetaLocalSurvival.StrongTopology
