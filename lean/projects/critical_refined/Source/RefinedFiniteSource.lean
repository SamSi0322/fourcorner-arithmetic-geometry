import CriticalRationalFibres
import CriticalBoundaryEight
import RefinedSupport.CriticalRefinedWave27

noncomputable section
namespace FourCorner.RefinedFiniteSource
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation CriticalRefinedWave27
open RationalPlaceFibreHom RationalPlaceTower QuadraticRationalPlaceFibre
variable {k : Type*} [Field k]
set_option maxHeartbeats 2000000
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (field k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (field k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (field k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

/-- One ACTUAL rational cover place with good original restricted coordinates
supplies the ORIGINAL signed pattern and its literal product square. The
three coordinates and the product root are evaluated at that SAME place. -/
theorem from_good_cover (i:k) (hi:i^2= -1) (h2:(2:k)≠0)
    (w:Place k (CriticalLiteralDouble.field k i)) (hw:w.IsRational)
    (hg:CriticalBadUnits.good i (w.restrict (field k i))) :
    ∃ beta x y z:k, SignedPattern i beta 1 x y z ∧
      x≠0 ∧ y≠0 ∧ z≠0 ∧ IsSquare (2*(z+x*y)) := by
  letI := CriticalLiteralDouble.separable k i h2
  let v:=w.restrict (field k i)
  have hv:v.IsRational := CriticalRationalFibres.restrict_rational w hw
  obtain ⟨ha0,hb0,hc0,hs0⟩ := CriticalBadUnits.ordered_nonzero i hi h2
  obtain ⟨ha,hb,hc,hs⟩ := hg
  let aa:v.toValuationSubring := ⟨a k i,(v.mem_iff_ord_nonneg ha0).mpr (by rw [ha])⟩
  let bb:v.toValuationSubring := ⟨b k i,(v.mem_iff_ord_nonneg hb0).mpr (by rw [hb])⟩
  let cc:v.toValuationSubring := ⟨c k i,(v.mem_iff_ord_nonneg hc0).mpr (by rw [hc])⟩
  let ss:v.toValuationSubring := ⟨a k i^2-1,(v.mem_iff_ord_nonneg hs0).mpr (by rw [hs])⟩
  have hshift:ss=aa^2-1 := by apply Subtype.ext;rfl
  have heB:bb^2-1=algebraMap k v.toValuationSubring i*(aa^2-1) := by
    apply Subtype.ext;exact (actual_critical_equations k i).1
  have heC:cc^2-1=algebraMap k v.toValuationSubring (1+i)*(aa^2-1) := by
    apply Subtype.ext;exact (actual_critical_equations k i).2
  have hSval:=congrArg (evaluate v hv) hshift
  have hBval:=congrArg (evaluate v hv) heB
  have hCval:=congrArg (evaluate v hv) heC
  simp only [map_sub,map_pow,map_one,map_mul,evaluate_constant] at hSval hBval hCval
  let u:v.toValuationSubring := 2*(cc+aa*bb)
  have hr : CriticalLiteralDouble.root k i^2=
      algebraMap (field k i) (CriticalLiteralDouble.field k i) (u:field k i) :=
    CriticalLiteralDouble.root_square k i
  let R:=rootAtPlace v u (CriticalLiteralDouble.root k i) hr w rfl
  have hR:R^2=baseInclusion v w rfl u := by
    apply Subtype.ext
    change (R:CriticalLiteralDouble.field k i)^2=(baseInclusion v w rfl u:CriticalLiteralDouble.field k i)
    rw [rootAtPlace_coe,baseInclusion_coe]
    exact hr
  have hlocal:=congrArg (evaluate w hw) hR
  rw [map_pow,evaluate_baseInclusion v hv w rfl hw] at hlocal
  have hsq:IsSquare (2*(evaluate v hv cc+evaluate v hv aa*evaluate v hv bb)) := by
    refine ⟨evaluate w hw R,?_⟩
    have he : evaluate v hv u=2*(evaluate v hv cc+evaluate v hv aa*evaluate v hv bb) := by
      simp only [u,map_mul,map_add,map_ofNat]
    simpa only [he,pow_two] using hlocal.symm
  refine ⟨evaluate v hv ss,evaluate v hv aa,evaluate v hv bb,evaluate v hv cc,?_,
    ResidueValuationFacts.evaluate_nonzero_of_ord_zero v hv aa ha0 ha,
    ResidueValuationFacts.evaluate_nonzero_of_ord_zero v hv bb hb0 hb,
    ResidueValuationFacts.evaluate_nonzero_of_ord_zero v hv cc hc0 hc,hsq⟩
  refine ⟨hi,ResidueValuationFacts.evaluate_nonzero_of_ord_zero v hv ss hs0 hs,?_,?_,?_⟩
  · linear_combination -hSval
  · linear_combination hBval-i*hSval
  · linear_combination hCval-(1+i)*hSval

 theorem refinedPattern_of_good_cover {p:ℕ} [Fact p.Prime]
    (i:ZMod p) (hi:i^2= -1) (h2:(2:ZMod p)≠0)
    (w:Place (ZMod p) (CriticalLiteralDouble.field (ZMod p) i)) (hw:w.IsRational)
    (hg:CriticalBadUnits.good i (w.restrict (field (ZMod p) i))) : RefinedPattern p := by
  obtain ⟨beta,x,y,z,hp,hx,hy,hz,hsq⟩:=from_good_cover i hi h2 w hw hg
  exact ⟨i,beta,1,x,y,z,hp,one_ne_zero,hx,hy,hz,by simpa only [one_mul] using hsq⟩

#print axioms from_good_cover
#print axioms refinedPattern_of_good_cover
end FourCorner.RefinedFiniteSource
