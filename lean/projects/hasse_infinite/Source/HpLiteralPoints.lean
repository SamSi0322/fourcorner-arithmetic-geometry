import HpLiteralSmooth
import ThetaPointAPI

namespace FourCorner.HpLiteralPoints
open AlgebraicGeometry CategoryTheory MvPolynomial HpLiteralProjective HpLiteralSmooth
noncomputable section
universe u
variable {K L : Type u} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false

def roots (p : K) (S : HasseNorms.LocalPoint L (algebraMap K L p)) : Fin 4 → L := ![S.u,S.v,S.w,S.t]

def evaluation (p : K) (S : HasseNorms.LocalPoint L (algebraMap K L p)) :
    HpLiteralProjective.affineRing K p 0 →ₐ[K] L :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (roots p S)) (by
    have hk : ThetaQuotientChart.affineIdeal (equation K p) 0 ≤
        RingHom.ker (MvPolynomial.aeval (roots p S)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have h0:=S.sqU
      have h1:=S.sqV
      have h2:=S.sqW
      have h3:=S.sqT
      fin_cases i
      all_goals simp [ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,equation,drop_table,
        roots,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]
      · rw [h1,h0];ring
      · rw [h2,h0];ring
      · rw [h3,h0];ring
    exact fun x hx=>hk hx)

def point (p : K) (S : HasseNorms.LocalPoint L (algebraMap K L p)) : Spec (.of L) ⟶ curve K p :=
  Spec.map (CommRingCat.ofHom (evaluation p S).toRingHom) ≫
    (chartIso K p 0).inv ≫
      (Proj.basicOpen (ThetaProjectiveModel.grading (equation K p) (homogeneous K p))
        (ThetaProjectiveModel.coordinate (equation K p) (homogeneous K p) 0)).ι

theorem point_over (p : K) (S : HasseNorms.LocalPoint L (algebraMap K L p)) :
    point p S ≫ toBase K p=Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  simp only [point,Category.assoc]
  rw [ThetaModelBase.chart_over_base,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (evaluation p S).comp_algebraMap

/-- Every actual Q-point on the literal Proj yields a nonzero homogeneous
Q5 source in a genuine chart, including every coordinate hyperplane. -/
theorem rational_point_source (p : ℚ) (f : Spec (.of ℚ) ⟶ curve ℚ p)
    (hf : f ≫ toBase ℚ p=𝟙 _) : Nonempty (HasseRationalSource.HomogeneousPoint p) := by
  have ho : f ≫ toBase ℚ p=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)) := by
    have hR : algebraMap ℚ ℚ=RingHom.id ℚ := Subsingleton.elim _ _
    rw [hR,CommRingCat.ofHom_id,Spec.map_id]
    exact hf
  obtain ⟨j,g,hg⟩ := ThetaPointAPI.point_affine_algebra (equation ℚ p) (homogeneous ℚ p) f ho
  let x := extend j (fun a=>g (ax p j a))
  have he := relations p j g
  have hpEq : algebraMap ℚ ℚ p=p := by simp
  rw [hpEq] at he
  refine ⟨⟨x 0,x 1,x 2,x 3,x 4,?_,he⟩⟩
  intro hn
  have hh : x j=0 := by fin_cases j <;> tauto
  have h1 : x j=1 := extend_self j _
  exact one_ne_zero (h1.symm.trans hh)

theorem family_no_literal_point (j : ℕ) :
    ¬∃f : Spec (.of ℚ) ⟶ curve ℚ (HpInfiniteArithmetic.p j),
      f ≫ toBase ℚ (HpInfiniteArithmetic.p j)=𝟙 _ := by
  rintro ⟨f,hf⟩
  obtain ⟨P⟩ := rational_point_source _ f hf
  exact (HpFamilyNoPoint.family_no_rational_point j).false
    (HasseProjectivePoint.ofHomogeneousPoint _ P)

/-- Actual points on the literal projective C_p at every finite completion. -/
theorem family_finite_point (q : ℕ) [Fact q.Prime] (j : ℕ) :
    ∃f : Spec (.of ℚ_[q]) ⟶ curve ℚ (HpInfiniteArithmetic.p j),
      f ≫ toBase ℚ (HpInfiniteArithmetic.p j)=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[q])) := by
  obtain ⟨S⟩ := (HpEverywhereLocal.family_Loc j).2 q
  exact ⟨point (K:=ℚ) (L:=ℚ_[q]) (HpInfiniteArithmetic.p j) S,point_over (K:=ℚ) (L:=ℚ_[q]) _ S⟩

/-- The actual strict-distance real source gives a point of the literal Proj. -/
theorem family_real_point (j : ℕ) :
    ∃f : Spec (.of ℝ) ⟶ curve ℚ (HpInfiniteArithmetic.p j),
      f ≫ toBase ℚ (HpInfiniteArithmetic.p j)=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ)) := by
  obtain ⟨S,_,_,_⟩ := HpStrictRealGeneric.family_strict_real_transcendental j
  exact ⟨point (K:=ℚ) (L:=ℝ) (HpInfiniteArithmetic.p j) S,point_over (K:=ℚ) (L:=ℝ) _ S⟩

#print axioms point
#print axioms point_over
#print axioms rational_point_source
#print axioms family_no_literal_point
#print axioms family_finite_point
#print axioms family_real_point
end
end FourCorner.HpLiteralPoints
