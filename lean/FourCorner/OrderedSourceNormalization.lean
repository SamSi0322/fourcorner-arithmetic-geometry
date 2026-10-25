import FourCorner.OrderedSource
import FourCorner.PurePointEquiv

namespace FourCorner

/-- Positive squarefree integer kernels. -/
def PositiveSquarefree := {n : ℕ // 0 < n ∧ Squarefree n}

/-- The full disjoint union, with no rank or finite-support restriction. -/
def AllNormalizedPure := Σ n : PositiveSquarefree, {s : PureCore (n.1 : ℚ) // PureMetric s}
def AllOrderedSources := Σ n : PositiveSquarefree, {s : OrderedCore (n.1 : ℚ) // OrderedMetric s}

/-- Forgetting the uniquely recoverable kernel and positive normalization. -/
def forgetNormalization (s : AllNormalizedPure) : PurePoint where
  p := s.2.1.p
  β := s.2.1.β
  U := s.2.1.U
  V := s.2.1.V
  W := s.2.1.W
  T := s.2.1.T
  h := s.2.1.pureCoordinates s.2.2

theorem forgetNormalization_injective : Function.Injective forgetNormalization := by
  rintro ⟨n, s, hs⟩ ⟨m, t, ht⟩ he
  have hp : s.p = t.p := congrArg PurePoint.p he
  have hβ : s.β = t.β := congrArg PurePoint.β he
  have hU : s.U = t.U := congrArg PurePoint.U he
  have hV : s.V = t.V := congrArg PurePoint.V he
  have hW : s.W = t.W := congrArg PurePoint.W he
  have hT : s.T = t.T := congrArg PurePoint.T he
  have heq : (n.1 : ℚ) * s.k ^ 2 = (m.1 : ℚ) * t.k ^ 2 := by
    rw [s.hk2, t.hk2, hp]
  have hn : n.1 = m.1 := squarefree_eq_of_rat_mul_sq_eq n.2.2 m.2.2 s.hk t.hk heq
  have hnm : n = m := Subtype.ext hn
  subst m
  have hk : s.k = t.k := positive_rat_square_factor_unique n.2.1 s.hk t.hk heq
  have hst : s = t := PureCore.ext hp hβ hk hU hV hW hT
  subst t
  rfl

theorem forgetNormalization_surjective : Function.Surjective forgetNormalization := by
  intro s
  obtain ⟨⟨n, k⟩, ⟨hn, hns, hk, hnk⟩, _⟩ := pureCoordinates_normalization s.h
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  let t : PureCore (n : ℚ) := {
    p := s.p, β := s.β, k := k, U := s.U, V := s.V, W := s.W, T := s.T
    hn := hnq, hp := s.h.hp, hβ := s.h.hβ, hk := hk
    hU := s.h.hUpos, hV := s.h.hVpos, hW := s.h.hWpos, hT := s.h.hTpos
    hk2 := hnk, hU2 := s.h.hU2, hV2 := s.h.hV2, hW2 := s.h.hW2, hT2 := s.h.hT2 }
  refine ⟨⟨⟨n, hn, hns⟩, ⟨t, s.h.hmetric⟩⟩, ?_⟩
  apply PurePoint.ext <;> rfl

/-- Every positive pure point has a unique squarefree normalization. -/
noncomputable def normalizationEquiv : AllNormalizedPure ≃ PurePoint :=
  Equiv.ofBijective forgetNormalization ⟨forgetNormalization_injective, forgetNormalization_surjective⟩

/-- Simultaneous normalization and actual ordered elliptic coordinates. -/
noncomputable def orderedPureGlobalEquiv : AllOrderedSources ≃ PurePoint :=
  (Equiv.sigmaCongrRight (fun n : PositiveSquarefree => orderedPureStrictEquiv (n.1 : ℚ))).trans
    normalizationEquiv

/-- Theorem thm:ell-exact-source: the entire positive squarefree disjoint union
is in bijection with the strict rational four-distance points in the chamber.
Both ordinates, both product roots, the final positive square root, and the
original strict metric are retained in AllOrderedSources. -/
noncomputable def exactOrderedSourceCorrespondence : AllOrderedSources ≃ ChamberPoint :=
  orderedPureGlobalEquiv.trans pureChamberEquiv

/-- Orientation matching the manuscript's statement, from strict original points. -/
noncomputable def strictChamberOrderedSourceCorrespondence : ChamberPoint ≃ AllOrderedSources :=
  exactOrderedSourceCorrespondence.symm

/-- The final-square identity for the point produced by the full bijection. -/
theorem exactOrderedSourceCorrespondence_final_square (s : AllOrderedSources) :
    (s.2.1.a + s.2.1.c) / (2 * (s.2.1.c + (s.1.1 : ℚ))) =
      1 / ((exactOrderedSourceCorrespondence s).r₀ +
        (exactOrderedSourceCorrespondence s).r₃) ^ 2 := by
  exact s.2.1.final_square

/-- Existence in the entire original square, before choosing a chamber. -/
theorem originalStrictPoint_iff_orderedSource :
    (∃ x y r₀ r₁ r₂ r₃ : ℚ, StrictPoint x y r₀ r₁ r₂ r₃) ↔
      Nonempty AllOrderedSources := by
  rw [originalStrictPoint_iff_purePoint]
  constructor
  · rintro ⟨p⟩
    exact ⟨orderedPureGlobalEquiv.symm p⟩
  · rintro ⟨s⟩
    exact ⟨orderedPureGlobalEquiv s⟩

#print axioms originalStrictPoint_iff_orderedSource
#print axioms exactOrderedSourceCorrespondence_final_square
#print axioms exactOrderedSourceCorrespondence
#print axioms strictChamberOrderedSourceCorrespondence
#print axioms forgetNormalization_injective
#print axioms forgetNormalization_surjective
#print axioms orderedPureGlobalEquiv
end FourCorner
