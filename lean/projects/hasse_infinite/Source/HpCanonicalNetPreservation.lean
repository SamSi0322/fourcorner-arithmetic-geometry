import HpCanonicalActionFormula
import HpQuadraticExpansion

namespace FourCorner.HpCanonicalNetPreservation
open AlgebraicCurve HpLiteralField HpFieldGeometry HpCanonicalForms HpCanonicalBasis HpCanonicalIsomorphism
  HpCanonicalActionFormula HpQuadraticRelations HpDiagonalNet HpQuadraticExpansion HpDiagonalKernelRigidity
noncomputable section
attribute [local instance] Classical.propDecidable
variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
local instance perfect : PerfectField K := IsAlgClosed.perfectField K
local instance finite (p : K) : FiniteDimensional (RatFunc K) (field K p) := finite_over_line K p
local instance curve (p : K) : IsCurveOver K (field K p) := isCurveOver K p
local instance finiteType (p : K) : Algebra.EssFiniteType K (field K p) := RatFuncFiniteExtension.essFiniteType K (field K p)
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule
variable {p q : K} (e : field K p ≃ₐ[K] field K q)
  (hp : p ≠ 0) (hpa : p-1 ≠ 0) (hpb : p+1 ≠ 0)
  (hq : q ≠ 0) (hqa : q-1 ≠ 0) (hqb : q+1 ≠ 0)

 theorem transformed_relation (d : Fin 5 → K) (hd : d∈net K p) :
    (∑i,algebraMap K (field K q) (d i)*(linearCoordinate K e hp hpa hpb hq hqa hqb i)^2)=0 := by
  obtain ⟨hds,hdi⟩ := (mem_net K p d).mp hd
  have hs : (∑i,algebraMap K (field K p) (d i)*(coordinate K p i)^2)=0 := by
    have hh := (quadratic_relation_iff K p hp hpa hpb d (fun _ => 0)).mpr ⟨by simp,hds,hdi⟩
    simpa using hh
  have he := congrArg e hs
  simp only [map_sum,map_mul,map_pow,AlgEquiv.commutes,map_zero] at he
  calc
    _=∑i,(algebraMap K (field K q) (d i)*(e (coordinate K p i))^2)*
        (linearCoordinate K e hp hpa hpb hq hqa hqb 4)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← coordinate_scaling K e hp hpa hpb hq hqa hqb i]
      ring
    _=(∑i,algebraMap K (field K q) (d i)*(e (coordinate K p i))^2)*
        (linearCoordinate K e hp hpa hpb hq hqa hqb 4)^2 := (Finset.sum_mul _ _ _).symm
    _=0 := by rw [he,zero_mul]

 theorem halfCross_zero (d : Fin 5 → K) (hd : d∈net K p) (jk : Pair) :
    halfCross d (matrix K e hp hpa hpb hq hqa hqb) jk=0 := by
  let M := matrix K e hp hpa hpb hq hqa hqb
  let f := algebraMap K (field K q)
  have he := quadratic_expansion (fun i => f (d i)) (fun j i => f (M j i)) (coordinate K q)
  have hg (j : Fin 5) : diagonal (fun i => f (d i)) (fun j i => f (M j i)) j=f (diagonal d M j) := by
    simp [diagonal,map_sum,map_mul,map_pow]
  have hc (ij : Pair) : 2*halfCross (fun i => f (d i)) (fun j i => f (M j i)) ij=f (2*halfCross d M ij) := by
    simp [halfCross,map_sum,map_mul,map_ofNat]
  simp_rw [hg,hc] at he
  have hr : (∑j,f (diagonal d M j)*coordinate K q j^2)+
      (∑ij,f (2*halfCross d M ij)*coordinate K q ij.val.1*coordinate K q ij.val.2)=0 := by
    rw [← he]
    exact transformed_relation K e hp hpa hpb hq hqa hqb d hd
  have hh := ((quadratic_relation_iff K q hq hqa hqb (diagonal d M) (fun ij => 2*halfCross d M ij)).mp hr).1 jk
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

/-- The actual canonical coordinate action preserves the intrinsic net of
quadrics. This identity is derived from the field isomorphism and exact
quadratic relations; it is not an extra rigidity hypothesis. -/
theorem net_preservation (d : Fin 5 → K) (hd : d∈net K p) :
    ∃b : Fin 5 → K,∀x y,
      pair d (transposeEquiv K (coordinateAction K e hp hpa hpb hq hqa hqb) x)
        (transposeEquiv K (coordinateAction K e hp hpa hpb hq hqa hqb) y)=pair b x y := by
  let M := matrix K e hp hpa hpb hq hqa hqb
  refine ⟨diagonal d M,?_⟩
  intro x y
  simp only [pair,transposeEquiv_apply]
  have hh := bilinear_expansion d M x y
  dsimp [M] at hh
  simp only [halfCross_zero K e hp hpa hpb hq hqa hqb d hd,zero_mul,Finset.sum_const_zero,add_zero] at hh
  simpa only [M,matrix,mul_comm] using hh

/-- Every original canonical axis is recovered intrinsically from the actual field. -/
theorem actual_inverse_axis (i : Fin 5) :
    ∃j : Fin 5,OnAxis j
      ((transposeEquiv K (coordinateAction K e hp hpa hpb hq hqa hqb)).symm (Pi.single i 1)) := by
  apply inverse_axis _ (net K p : Set (Fin 5 → K))
  · intro j
    obtain ⟨d,hd,hi,hn⟩ := HpAxisQuadrics.exists_unique_zero_coefficient K p hp hpa hpb j
    exact ⟨d,hd,hi,hn⟩
  · exact net_preservation K e hp hpa hpb hq hqa hqb

#print axioms transformed_relation
#print axioms halfCross_zero
#print axioms net_preservation
#print axioms actual_inverse_axis
end
end FourCorner.HpCanonicalNetPreservation
