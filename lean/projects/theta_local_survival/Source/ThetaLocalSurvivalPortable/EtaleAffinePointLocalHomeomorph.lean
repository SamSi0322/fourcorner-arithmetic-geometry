import ThetaLocalSurvivalPortable.PresentationImplicitSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
open MvPolynomial
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (A S K : Type) [CommRing A] [CommRing S] [Algebra ℚ A]
  [Algebra A S] [Algebra ℚ S] [IsScalarTower ℚ A S]
  [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K]
  {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
  (G : Algebra.Generators ℚ A α) (P : Algebra.SubmersivePresentation A S β β)

/-- The actual presentation solution space is the actual analytic equation graph. -/
def presentationGraphHomeomorph : presentationSolutions ℚ A K S P.toPresentation ≃ₜ
    equationGraph (generatorCoordinates ℚ A K G) (polynomialSystem (analyticRelation A S K G P)) := by
  apply Homeomorph.setCongr
  ext q
  change (∀ i,eval₂ q.1.toRingHom q.2 (P.relation i)=0) ↔
    polynomialSystem (analyticRelation A S K G P) (generatorCoordinates ℚ A K G q.1,q.2)=0
  rw [polynomialSystem_actual_equations]
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

/-- The actual affine S(K), in its evaluation topology, is the same analytic equation graph. -/
def actualPresentationGraphHomeomorph : (S →ₐ[ℚ] K) ≃ₜ
    equationGraph (generatorCoordinates ℚ A K G) (polynomialSystem (analyticRelation A S K G P)) :=
  (presentationPointsHomeomorph ℚ A K S P.toPresentation).trans
    (presentationGraphHomeomorph A S K G P)

include G in
/-- Local analytic inverse for the actual map S(K)→A(K) of any actual square submersive
presentation, with the unit Jacobian proved algebraically. -/
theorem isLocalHomeomorph_actualPresentationBase (hP : P.map=id) :
    IsLocalHomeomorph (actualPresentationBase A S K) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro f
  obtain ⟨e,hu,he⟩ := actual_presentation_implicit_chart A S K G P hP f
  let H := actualPresentationGraphHomeomorph A S K G P
  let T := {q : equationGraph (generatorCoordinates ℚ A K G)
    (polynomialSystem (analyticRelation A S K G P)) |
      (generatorCoordinates ℚ A K G q.1.1,q.1.2)∈e.source}
  let U : Set (S →ₐ[ℚ] K) := H ⁻¹' T
  have hT : IsOpen T := isOpen_equationGraphSource _ _ e (continuous_generatorCoordinates ℚ A K G)
  have hU : IsOpen U := hT.preimage H.continuous
  have hfU : f∈U := hu
  let H' : U ≃ₜ T := H.subtype (fun _ => Iff.rfl)
  have hE := isOpenEmbedding_equationGraphProjection _ _ e he
    (continuous_generatorCoordinates ℚ A K G)
  refine ⟨U,hU.mem_nhds hfU,?_⟩
  exact hE.comp H'.isOpenEmbedding

/-- Every genuine etale finite-type affine map over QQ induces a local homeomorphism
on actual K-points for every complete nontrivially normed field K, including Q_p. -/
theorem etale_affine_points_localHomeomorph [Algebra.FiniteType ℚ A] [Algebra.Etale A S] :
    IsLocalHomeomorph (fun f : S →ₐ[ℚ] K => f.comp (Algebra.algHom ℚ A S)) := by
  obtain ⟨α,hα,g,hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType ℚ A)
  letI := hα
  let G : Algebra.Generators ℚ A α := Algebra.Generators.ofAlgHom g hg
  obtain ⟨β,hβ,P,hP⟩ := etale_exists_square_presentation A S
  letI := Fintype.ofFinite β
  letI : DecidableEq β := Classical.decEq β
  exact isLocalHomeomorph_actualPresentationBase A S K G P hP

end FourCorner.ThetaLocalSurvival.StrongTopology
