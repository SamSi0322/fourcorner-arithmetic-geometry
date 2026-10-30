import ThetaCoverClassPortable.CompactGraphProjection
import Mathlib.Topology.MetricSpace.ProperSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (A S K : Type) [CommRing A] [CommRing S] [Algebra ℚ A]
  [Algebra A S] [Algebra ℚ S] [IsScalarTower ℚ A S]
  [NontriviallyNormedField K] [Algebra ℚ K]
  {ι σ : Type} [Fintype ι] (P : Algebra.Presentation A S ι σ)

/-- The actual defining equations cut out a closed subspace of coefficient points and variables. -/
theorem isClosed_presentationSolutions :
    IsClosed {q : (A →ₐ[ℚ] K) × (ι→K) | ∀ i, MvPolynomial.eval₂ q.1.toRingHom q.2 (P.relation i)=0} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun i => isClosed_eq (continuous_eval₂_point ℚ A K (P.relation i)) continuous_const)

/-- Actual variables of a module-finite algebra presentation are locally uniformly bounded
over A(K); all annihilating polynomials and bounds are derived from module finiteness. -/
theorem finite_algebra_presentation_locally_bounded [Module.Finite A S] (φ : A →ₐ[ℚ] K) :
    ∃ (U : Set (A →ₐ[ℚ] K)) (C : NNReal), IsOpen U ∧ φ∈U ∧
      ∀ f : S →ₐ[ℚ] K, f.comp (Algebra.algHom ℚ A S)∈U → ‖fun i => f (P.val i)‖₊≤C := by
  have hints (i : ι) : IsIntegral A (P.val i) := Algebra.IsIntegral.isIntegral _
  choose U C hU hφ hbd using fun i => integral_element_locally_bounded A K S (P.val i) (hints i) φ
  refine ⟨⋂ i,U i,Finset.univ.sup C,isOpen_iInter_of_finite (fun i => hU i),Set.mem_iInter.mpr hφ,?_⟩
  intro f hf
  apply pi_nnnorm_le_iff.mpr
  intro i
  exact (hbd i f (Set.mem_iInter.mp hf i)).trans (Finset.le_sup (f:=C) (Finset.mem_univ i))

variable [ProperSpace K]

/-- The actual presentation solution space of a finite algebra has compact vertical
confinement above a genuine neighborhood of every actual base point. -/
theorem finite_algebra_solutions_compact_bound [Module.Finite A S] (φ : A →ₐ[ℚ] K) :
    ∃ U∈𝓝 φ,∃ C : Set (ι→K), IsCompact C ∧
      ∀ q∈{q : (A →ₐ[ℚ] K) × (ι→K) | ∀ i, MvPolynomial.eval₂ q.1.toRingHom q.2 (P.relation i)=0},
        q.1∈U → q.2∈C := by
  obtain ⟨U,C,hU,hφ,hb⟩ := finite_algebra_presentation_locally_bounded A S K P φ
  refine ⟨U,hU.mem_nhds hφ,Metric.closedBall 0 (C : ℝ),isCompact_closedBall _ _,?_⟩
  intro q hq hqU
  let z : presentationSolutions ℚ A K S P := ⟨q,hq⟩
  let f := presentationSolutionLift ℚ A K S P z
  have hf : presentationPointCoordinates ℚ A K S P f=z := (presentationPointEquiv ℚ A K S P).apply_symm_apply z
  have hb' : f.comp (Algebra.algHom ℚ A S)=q.1 := congrArg (fun x => x.1.1) hf
  have hx : (fun i => f (P.val i))=q.2 := congrArg (fun x => x.1.2) hf
  have hnorm := hb f (hb'.symm ▸ hqU)
  rw [hx] at hnorm
  rw [Metric.mem_closedBall,dist_zero_right]
  exact_mod_cast hnorm

/-- Projection of the actual solution space of any finite algebra is a closed map on local fields. -/
theorem finite_algebra_solution_projection_closed [Module.Finite A S] :
    IsClosedMap (fun q : presentationSolutions ℚ A K S P => q.1.1) :=
  closed_projection_of_local_compact_bounds _ (isClosed_presentationSolutions A S K P)
    (finite_algebra_solutions_compact_bound A S K P)

end FourCorner.ThetaLocalSurvival.StrongTopology
