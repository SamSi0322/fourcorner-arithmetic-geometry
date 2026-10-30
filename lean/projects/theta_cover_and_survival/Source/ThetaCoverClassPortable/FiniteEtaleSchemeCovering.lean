import ThetaCoverClassPortable.FiniteEtaleFullAffinePreimage
import ThetaCoverClassPortable.CoveringOpenCharts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal

variable (K : Type) [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K] [ProperSpace K]
  {X Y : Over base} (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] [LocallyOfFiniteType Y.hom]

/-- Every actual finite etale morphism of locally finite-type QQ schemes is an actual
covering map on canonical strong-topology local-field points. -/
theorem finite_etale_scheme_points_covering :
    IsCoveringMap (fun P : KPoints K X => P≫f) := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  intro P _
  obtain ⟨A,jA,p,hjA,hp⟩ := exists_affine_chart_through_point K Y P
  letI := hjA
  obtain ⟨B,jB,q,hjB,hqf,hqe,hcomm,hrange⟩ := finite_etale_full_affine_preimage K f A jA
  letI := hjB
  letI := hqf
  letI := hqe
  letI : LocallyOfFiniteType (pointObject A).hom := by rw [←jA.w]; infer_instance
  have hq := finite_etale_affine_scheme_points_covering K A B q
  have hc : ∀ Q : KPoints K (pointObject B),(Q≫jB)≫f=(Q≫q)≫jA := by
    intro Q
    rw [Category.assoc,Category.assoc,hcomm]
  have h := covering_on_open_charts (fun P : KPoints K X => P≫f)
    (fun Q : KPoints K (pointObject B) => Q≫jB)
    (fun Q : KPoints K (pointObject A) => Q≫jA)
    (fun Q : KPoints K (pointObject B) => Q≫q)
    (continuous_pointMap K f) (isOpenEmbedding_pointMap K jB) (isOpenEmbedding_pointMap K jA)
    hq hc hrange
  exact h P ⟨pointChange p,hp⟩

end FourCorner.ThetaLocalSurvival.StrongTopology
