import FourCorner.RadiusContent

namespace FourCorner.IntegralModel

/-- The centered sum of squares, factored by the square of the common radius
content. -/
theorem content_center_identity (M : IntegralModel) :
    (2 * M.X - M.L)^2 + (2 * M.Y - M.L)^2 =
      (M.radiusContent : ℤ)^2 *
        (4 * (M.A₀ / (M.radiusContent : ℤ))^2 -
          4 * M.reducedSide * (M.X + M.Y) +
          2 * (M.radiusContent : ℤ)^2 * M.reducedSide^2) := by
  have hA : (M.radiusContent : ℤ) * (M.A₀ / (M.radiusContent : ℤ)) = M.A₀ :=
    Int.mul_ediv_cancel' M.radiusContent_dvd₀
  calc
    (2 * M.X - M.L)^2 + (2 * M.Y - M.L)^2 =
        4 * M.A₀^2 - 4 * M.L * (M.X + M.Y) + 2 * M.L^2 := by
      nlinarith [M.sq₀]
    _ = 4 * ((M.radiusContent : ℤ) * (M.A₀ / (M.radiusContent : ℤ)))^2 -
        4 * ((M.radiusContent : ℤ)^2 * M.reducedSide) * (M.X + M.Y) +
        2 * ((M.radiusContent : ℤ)^2 * M.reducedSide)^2 := by
      rw [hA, M.reducedSide_factorization]
    _ = _ := by ring

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.content_center_identity
