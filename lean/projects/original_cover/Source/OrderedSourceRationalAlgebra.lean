import OrderedSourceFunctionField
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource.RationalAlgebra
variable {F : Type*} [Field F] [CharZero F]
def CongruentEquation (n x y : F) : Prop := y^2=x*(x-n)*(x+n)
def ordinateW (n b ℓ u v : F) : F := b * ℓ / (n * u * v)
def pairP (n a : F) : F := -n / a
def pairK (a b : F) : F := b / a ^ 2
def pairBeta (n c : F) : F := (c + n) / (c - n)
def pairU (n a b ℓ u v : F) : F := (n - a) * ordinateW n b ℓ u v / (b * v)
def pairV (a b v : F) : F := -(2 * b) / (a * v)
def pairW (n a u v : F) : F := 2 * (a - n) * u / (a * v)
def pairT (n a b ℓ u v h : F) : F := 2 * pairU n a b ℓ u v * h

theorem ordinateW_square {n a b c ℓ u v : F}
    (hn : n ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (ham : a - n ≠ 0) (hcm : c - n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c ℓ)
    (hu : u ^ 2 = -(a * c) / n) (hv : v ^ 2 = -((a - n) * (c - n)) / n) :
    ordinateW n b ℓ u v ^ 2 = (a + n) * (c + n) := by
  unfold ordinateW
  simp only [div_pow, mul_pow]
  rw [hQ, hR, hu, hv]
  field_simp
  <;> ring

theorem pairK_square {n a b : F} (ha : a ≠ 0)
    (hQ : CongruentEquation n a b) :
    n * pairK a b ^ 2 = pairP n a * (pairP n a ^ 2 - 1) := by
  unfold pairK pairP
  simp only [div_pow]
  rw [hQ]
  field_simp
  <;> ring

theorem pairU_square {n a b c ℓ u v : F}
    (ha : a ≠ 0) (ham : a - n ≠ 0) (hap : a + n ≠ 0) (hcm : c - n ≠ 0)
    (hn : n ≠ 0) (hQ : CongruentEquation n a b)
    (hv : v ^ 2 = -((a - n) * (c - n)) / n)
    (hw : ordinateW n b ℓ u v ^ 2 = (a + n) * (c + n)) :
    pairU n a b ℓ u v ^ 2 = pairP n a * pairBeta n c := by
  unfold pairU pairP pairBeta
  simp only [div_pow, mul_pow]
  rw [hw, hQ, hv]
  field_simp
  <;> ring

theorem pairV_square {n a b c v : F}
    (ha : a ≠ 0) (ham : a - n ≠ 0) (hcm : c - n ≠ 0)
    (hn : n ≠ 0) (hQ : CongruentEquation n a b)
    (hv : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairV a b v ^ 2 = 2 * (pairP n a - 1) * (pairBeta n c - 1) := by
  unfold pairV pairP pairBeta
  simp only [div_pow, neg_sq, mul_pow]
  rw [hQ, hv]
  field_simp
  <;> ring

theorem pairW_square {n a c u v : F}
    (ha : a ≠ 0) (ham : a - n ≠ 0) (hcm : c - n ≠ 0)
    (hn : n ≠ 0) (hu : u ^ 2 = -(a * c) / n)
    (hv : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairW n a u v ^ 2 = 2 * (pairP n a + 1) * (pairBeta n c + 1) := by
  unfold pairW pairP pairBeta
  simp only [div_pow, mul_pow]
  rw [hu, hv]
  field_simp
  <;> ring

theorem pairT_square {n a b c ℓ u v h : F}
    (ha : a ≠ 0) (hcm : c - n ≠ 0) (hcp : c + n ≠ 0)
    (hU : pairU n a b ℓ u v ^ 2 = pairP n a * pairBeta n c)
    (hh : h ^ 2 = (a + c) / (2 * (c + n))) :
    pairT n a b ℓ u v h ^ 2 =
      (pairP n a - 1) * pairBeta n c + pairP n a + 1 := by
  unfold pairT
  simp only [mul_pow]
  rw [hU, hh]
  unfold pairP pairBeta
  field_simp
  <;> ring

/-- Cancellation of the first product root uses the ordered second slot. -/
theorem pairU_simplified {n a b c ℓ u v : F}
    (hn : n ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hcm : c - n ≠ 0)
    (hv2 : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairU n a b ℓ u v = ℓ / (u * (c - n)) := by
  have hvn : n * v ^ 2 = -((a - n) * (c - n)) := by
    have hh := (eq_div_iff hn).mp hv2
    linear_combination hh
  unfold pairU ordinateW
  field_simp
  linear_combination -ℓ * hvn

theorem pairT_square_simplified {n a b c ℓ u v h : F}
    (ha : a ≠ 0) (hcm : c - n ≠ 0)
    (hT : pairT n a b ℓ u v h ^ 2 =
      (pairP n a - 1) * pairBeta n c + pairP n a + 1) :
    pairT n a b ℓ u v h ^ 2 = -2 * n * (a + c) / (a * (c - n)) := by
  rw [hT]
  unfold pairP pairBeta
  field_simp
  <;> ring

theorem pairWV_simplified {n a b c u v : F}
    (hn : n ≠ 0) (ha : a ≠ 0) (hv : v ≠ 0) (hcm : c - n ≠ 0)
    (hv2 : v ^ 2 = -((a - n) * (c - n)) / n) :
    pairW n a u v * pairV a b v = 4 * b * n * u / (a ^ 2 * (c - n)) := by
  have hvn : n * v ^ 2 = -((a - n) * (c - n)) := by
    have hh := (eq_div_iff hn).mp hv2
    linear_combination hh
  unfold pairW pairV
  field_simp
  linear_combination -4 * b * u * hvn

/-- Both real-metric contributions use the same original pair and the same u. -/
theorem pair_metric_identity {n a b c ℓ u v h : F}
    (hn : n ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hu : u ≠ 0) (hac : a + c ≠ 0) (hcm : c - n ≠ 0)
    (hU : pairU n a b ℓ u v = ℓ / (u * (c - n)))
    (hWV : pairW n a u v * pairV a b v = 4 * b * n * u / (a ^ 2 * (c - n)))
    (hT : pairT n a b ℓ u v h ^ 2 = -2 * n * (a + c) / (a * (c - n)))
    (hu2 : u ^ 2 = -(a * c) / n) :
    (4 * pairU n a b ℓ u v + pairW n a u v * pairV a b v) /
        pairT n a b ℓ u v h ^ 2 =
      (2 * u / (a + c)) * (-b / a + ℓ / c) := by
  rw [hU, hWV, hT]
  have hun : n * u ^ 2 = -(a * c) := by
    have hh := (eq_div_iff hn).mp hu2
    linear_combination hh
  field_simp
  linear_combination -4 * a * ℓ * hun


/-- Literal returned original coordinates, with all four ordered radii. -/
def pureReturn (U V W T : F) : Fin 6 → F :=
 ![1/2+(U+W*V/4)/T^2,1/2+(U-W*V/4)/T^2,
   (U+1)/T,(W-V)/(2*T),(W+V)/(2*T),(U-1)/T]

theorem pureReturn_relations (p beta U V W T : F) (hT : T≠0)
    (hU : U^2=p*beta) (hV : V^2=2*(p-1)*(beta-1))
    (hW : W^2=2*(p+1)*(beta+1)) (hTs : T^2=(p-1)*beta+p+1) :
    ∀i,originalRelations (pureReturn U V W T) i=0 := by
  have hm : 8*(U^2+1)*T^2=4*(T^2)^2+16*U^2+W^2*V^2 := by
    rw [hU,hV,hW,hTs]; ring
  have hs : W^2+V^2=4*U^2+4 := by rw [hW,hV,hU]; ring
  intro i; fin_cases i <;> simp [originalRelations,pureReturn]
  all_goals field_simp
  · linear_combination 8*hm
  · linear_combination 8*hm+16*T^2*hs
  · linear_combination 8*hm+16*T^2*hs
  · linear_combination 8*hm

/-- The pure parameters are rational expressions in the actual returned radii. -/
theorem pureReturn_parameters (p beta U V W T : F) (hT : T≠0) (hp : p≠0)
    (hU : U^2=p*beta) (hV : V^2=2*(p-1)*(beta-1))
    (hTs : T^2=(p-1)*beta+p+1) :
    let r:=pureReturn U V W T
    (2-(r 4-r 3)^2)/(r 2-r 5)^2=p ∧
    (r 2+r 5)^2/(2-(r 4-r 3)^2)=beta := by
  dsimp only
  have hd : pureReturn U V W T 2-pureReturn U V W T 5=2/T := by simp [pureReturn]; ring
  have he : pureReturn U V W T 4-pureReturn U V W T 3=V/T := by simp [pureReturn]; ring
  have hs : pureReturn U V W T 2+pureReturn U V W T 5=2*U/T := by simp [pureReturn]; ring
  have hden : 2-(V/T)^2=4*p/T^2 := by
    field_simp
    linear_combination 2*hTs-hV
  rw [hd,he,hs,hden]
  constructor
  · field_simp; norm_num
  · field_simp
    linear_combination 4*hU

#print axioms pureReturn_parameters
#print axioms pureReturn_relations
end FourCorner.OriginalCoverCompletion.OrderedSource.RationalAlgebra
