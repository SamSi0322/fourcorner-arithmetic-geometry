import FourCorner.OrderedSourceNormalization
import FourCorner.RationalSquarefreeKernel
import FourCorner.KernelStrict
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace FourCorner.SourceLayer17

def radiusProduct (r₀ r₁ r₂ r₃ : ℚ) : ℚ := r₀*r₃+r₁*r₂

theorem pure_product_class {n : ℚ} (s : PureCore n) :
    let t := radiusProduct (pureR0 s.U s.T) (pureR1 s.V s.W s.T)
      (pureR2 s.V s.W s.T) (pureR3 s.U s.T)
    ∃ w : ℚ, 0 < w ∧ t^2-1 = n*w^2 := by
  dsimp
  let D := s.p^2-1
  have hD : 0 < D := by dsimp [D]; nlinarith [s.hp]
  have hT := ne_of_gt s.hT
  have hDn := ne_of_gt hD
  refine ⟨s.k*s.V*s.W/(D*s.T^2), div_pos (mul_pos (mul_pos s.hk s.hV) s.hW)
    (mul_pos hD (sq_pos_of_pos s.hT)), ?_⟩
  have hVW : s.V^2*s.W^2 = 4*D*(s.β^2-1) := by rw [s.hV2,s.hW2]; dsimp [D]; ring
  have ht : radiusProduct (pureR0 s.U s.T) (pureR1 s.V s.W s.T)
      (pureR2 s.V s.W s.T) (pureR3 s.U s.T) =
      ((s.p+1)*s.β+s.p-1)/s.T^2 := by
    unfold radiusProduct pureR0 pureR1 pureR2 pureR3
    field_simp
    nlinarith [s.hU2,s.hV2,s.hW2]
  rw [ht]
  field_simp
  have hk := s.hk2
  change n*s.k^2 = s.p*D at hk
  have hpoly : (((s.p+1)*s.β+s.p-1)^2-s.T^4)*D^2 =
      n*s.k^2*(s.V^2*s.W^2) := by
    rw [hk,hVW,show s.T^4=(s.T^2)^2 by ring,s.hT2]
    dsimp [D]
    ring
  nlinarith [hpoly]

theorem ordered_kernel (s : AllOrderedSources) :
    rationalSquarefreePart
      ((radiusProduct (exactOrderedSourceCorrespondence s).r₀
      (exactOrderedSourceCorrespondence s).r₁ (exactOrderedSourceCorrespondence s).r₂
      (exactOrderedSourceCorrespondence s).r₃)^2-1) = s.1.1 := by
  obtain ⟨w,hw,he⟩ := pure_product_class s.2.1.toPure
  apply rationalSquarefreePart_eq_of_decomposition _ s.1.2.2 hw he
  rw [he]
  exact mul_pos (by exact_mod_cast s.1.2.1) (sq_pos_of_pos hw)

/-- A chamber point produces the full ordered source with its canonical kernel. -/
theorem chamber_source (c : ChamberPoint) :
    ∃ s : AllOrderedSources, exactOrderedSourceCorrespondence s = c ∧
      s.1.1 = rationalSquarefreePart ((radiusProduct c.r₀ c.r₁ c.r₂ c.r₃)^2-1) ∧
      (s.2.1.a+s.2.1.c)/(2*(s.2.1.c+(s.1.1:ℚ))) = 1/(c.r₀+c.r₃)^2 := by
  let s := strictChamberOrderedSourceCorrespondence c
  have he : exactOrderedSourceCorrespondence s = c :=
    exactOrderedSourceCorrespondence.apply_symm_apply c
  refine ⟨s,he,?_,?_⟩
  · simpa only [he] using (ordered_kernel s).symm
  · simpa only [he] using exactOrderedSourceCorrespondence_final_square s

/-- Chamber placement preserves precisely the parameter t in the corollary. -/
theorem chamber_preserving_product {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    ∃ c : ChamberPoint, radiusProduct c.r₀ c.r₁ c.r₂ c.r₃ = radiusProduct r₀ r₁ r₂ r₃ ∧
      c.r₀+c.r₃ = r₀+r₃ := by
  have upper : ∀ {x y r₀ r₁ r₂ r₃ : ℚ}, StrictPoint x y r₀ r₁ r₂ r₃ →
      1 < x+y → ∃ c : ChamberPoint,
      radiusProduct c.r₀ c.r₁ c.r₂ c.r₃ = radiusProduct r₀ r₁ r₂ r₃ ∧
      c.r₀+c.r₃ = r₀+r₃ := by
    intro x y r₀ r₁ r₂ r₃ h hs
    rcases lt_or_gt_of_ne (strict_point_not_diagonal h) with hlt | hgt
    · refine ⟨⟨y,x,r₀,r₂,r₁,r₃,strict_point_exchange h,by linarith,hlt⟩,?_⟩
      constructor
      · dsimp [radiusProduct]; ring
      · rfl
    · exact ⟨⟨x,y,r₀,r₁,r₂,r₃,h,hs,hgt⟩,rfl,rfl⟩
  rcases lt_or_gt_of_ne (strict_point_not_antidiagonal h) with hlt | hgt
  · obtain ⟨c,hc,hs⟩ := upper (strictPoint_centralRotation h) (by linarith)
    refine ⟨c,hc.trans ?_,hs.trans (add_comm _ _)⟩
    unfold radiusProduct; ring
  · exact upper h hgt

theorem original_t_gt_one {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) : 1 < radiusProduct r₀ r₁ r₂ r₃ :=
  strict_point_kernel_gt_one h

/-- Actual original strict data, canonical sf(t²−1), both elliptic ordinates,
all three positive roots, strict metric, and literal rational final square. -/
theorem original_source {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    ∃ s : AllOrderedSources,
      s.1.1 = rationalSquarefreePart ((radiusProduct r₀ r₁ r₂ r₃)^2-1) ∧
      (s.2.1.a+s.2.1.c)/(2*(s.2.1.c+(s.1.1:ℚ))) = 1/(r₀+r₃)^2 ∧
      IsSquare ((s.2.1.a+s.2.1.c)/(2*(s.2.1.c+(s.1.1:ℚ)) )) := by
  obtain ⟨c,hc,hs⟩ := chamber_preserving_product h
  obtain ⟨s,_,hn,hf⟩ := chamber_source c
  refine ⟨s,by simpa only [hc] using hn,by simpa only [hs] using hf,?_⟩
  exact ⟨s.2.1.h, by rw [←s.2.1.hh2]; ring⟩

/-- The first and second actual affine points retain the original slot order. -/
def firstPoint {n : ℚ} (s : OrderedCore n) : (congruentCurve n).toAffine.Point :=
  .some s.a s.b s.first_nonsingular

def secondPoint {n : ℚ} (s : OrderedCore n) : (congruentCurve n).toAffine.Point :=
  .some s.c s.ℓ s.second_nonsingular

/-- Canonical rational field embedding applied to each actual finite point. -/
def localFirst {K : Type*} [Field K] [CharZero K]
    {n : ℚ} (s : OrderedCore n) :
    ((congruentCurve n).toAffine.map (algebraMap ℚ K)).Point :=
  .some (s.a : K) (s.b : K)
    (((congruentCurve n).toAffine.map_nonsingular (algebraMap ℚ K).injective s.a s.b).mpr
      s.first_nonsingular)

def localSecond {K : Type*} [Field K] [CharZero K]
    {n : ℚ} (s : OrderedCore n) :
    ((congruentCurve n).toAffine.map (algebraMap ℚ K)).Point :=
  .some (s.c : K) (s.ℓ : K)
    (((congruentCurve n).toAffine.map_nonsingular (algebraMap ℚ K).injective s.c s.ℓ).mpr
      s.second_nonsingular)

/-- Literal return function in any characteristic-zero field, via the canonical
rational embedding. In particular, its displayed denominator remains nonzero. -/
theorem field_source {K : Type*} [Field K] [CharZero K]
    {n : ℚ} (s : OrderedCore n) :
    (s.b : K)^2 = (s.a : K)*((s.a : K)-(n : K))*((s.a : K)+(n : K)) ∧
    (s.ℓ : K)^2 = (s.c : K)*((s.c : K)-(n : K))*((s.c : K)+(n : K)) ∧
    (s.u : K)^2 = -((s.a : K)*(s.c : K))/(n : K) ∧
    (s.v : K)^2 = -(((s.a : K)-(n : K))*((s.c : K)-(n : K)))/(n : K) ∧
    ((s.a : K)+(s.c : K))/(2*((s.c : K)+(n : K))) ≠ 0 ∧
    IsSquare (((s.a : K)+(s.c : K))/(2*((s.c : K)+(n : K)))) := by
  have hQ := congrArg (algebraMap ℚ K) s.hQ
  have hR := congrArg (algebraMap ℚ K) s.hR
  have hu := congrArg (algebraMap ℚ K) s.hu2
  have hv := congrArg (algebraMap ℚ K) s.hv2
  have hh := congrArg (algebraMap ℚ K) s.hh2
  change (algebraMap ℚ K) (s.b^2) = (algebraMap ℚ K) (s.a*(s.a-n)*(s.a+n)) at hQ
  change (algebraMap ℚ K) (s.ℓ^2) = (algebraMap ℚ K) (s.c*(s.c-n)*(s.c+n)) at hR
  simp only [map_pow, map_div₀, map_neg, map_mul, map_sub, map_add, map_ofNat] at hQ hR hu hv hh
  change (s.h : K)^2 = ((s.a : K)+(s.c : K))/(2*((s.c : K)+(n : K))) at hh
  refine ⟨hQ,hR,hu,hv,?_,?_⟩
  · rw [←hh]
    exact pow_ne_zero 2 (by exact_mod_cast (ne_of_gt s.hh))
  · refine ⟨(s.h : K),?_⟩
    rw [←hh]; ring

local instance : Fact (Nat.Prime 113) := ⟨by decide⟩

/-- The exact three local square tests required by thm:cs-15569. -/
theorem three_local_squares {n : ℚ} (s : OrderedCore n) :
    IsSquare (((s.a : ℚ_[2])+(s.c : ℚ_[2]))/(2*((s.c : ℚ_[2])+(n : ℚ_[2])))) ∧
    IsSquare (((s.a : ℚ_[3])+(s.c : ℚ_[3]))/(2*((s.c : ℚ_[3])+(n : ℚ_[3])))) ∧
    IsSquare (((s.a : ℚ_[113])+(s.c : ℚ_[113]))/(2*((s.c : ℚ_[113])+(n : ℚ_[113])))) := by
  exact ⟨(field_source (K := ℚ_[2]) s).2.2.2.2.2,
    (field_source (K := ℚ_[3]) s).2.2.2.2.2,
    (field_source (K := ℚ_[113]) s).2.2.2.2.2⟩

end FourCorner.SourceLayer17
#print axioms FourCorner.SourceLayer17.pure_product_class
#print axioms FourCorner.SourceLayer17.ordered_kernel
#print axioms FourCorner.SourceLayer17.chamber_source
#print axioms FourCorner.SourceLayer17.chamber_preserving_product
#print axioms FourCorner.SourceLayer17.original_source

#print axioms FourCorner.SourceLayer17.field_source
#print axioms FourCorner.SourceLayer17.three_local_squares

#print axioms FourCorner.SourceLayer17.localFirst
#print axioms FourCorner.SourceLayer17.localSecond

#print axioms FourCorner.SourceLayer17.original_t_gt_one
