import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Definitions for the four-variable Filippov system (Cor. C.3 of the DFS paper)

State `z = (x₁, x₂, y₁, y₂) : Fin 4 → ℝ`, with `u = x₁ - x₂`, `v = y₁ - y₂`,
`E = exp (u⁺ + v⁺)`. Sums over `i = 1..K` are written with `j = i - 1 ∈ Finset.range K`.

The Filippov set at `z` is `{F θ η z}` with `θ, η ∈ [0,1]`, `θ = 1` if `u > 0`, `θ = 0` if
`u < 0`, and likewise `η` for `v`: the x-equations contain only the u-indicator, the y-equations
only the v-indicator, and the field is affine in each, so the convex hull of the one-sided limits
is exactly this set.
-/

noncomputable section
open Real

namespace DFS

/-- `u = x₁ - x₂`. -/
def u (z : Fin 4 → ℝ) : ℝ := z 0 - z 1
/-- `v = y₁ - y₂`. -/
def v (z : Fin 4 → ℝ) : ℝ := z 2 - z 3
/-- `E = exp (u⁺ + v⁺)`. -/
def E (z : Fin 4 → ℝ) : ℝ := exp (max (u z) 0 + max (v z) 0)

variable (N K : ℕ)

/-- `D₁ = e^{x₁} + e^{y₁} + N - 2`. -/
def D1 (z : Fin 4 → ℝ) : ℝ := exp (z 0) + exp (z 2) + (N : ℝ) - 2
/-- `D_{2,i} = (K-i+1) e^{x₁} + (i-1) E + e^{y₁} + N - K - 1`, with `j = i - 1`. -/
def D2 (j : ℕ) (z : Fin 4 → ℝ) : ℝ :=
  ((K : ℝ) - j) * exp (z 0) + (j : ℝ) * E z + exp (z 2) + (N : ℝ) - K - 1
/-- `D₃ = e^{y₁} + N - 1`. -/
def D3 (z : Fin 4 → ℝ) : ℝ := exp (z 2) + (N : ℝ) - 1
/-- `D₄ = K E + e^{y₁} + N - K - 1`. -/
def D4 (z : Fin 4 → ℝ) : ℝ := (K : ℝ) * E z + exp (z 2) + (N : ℝ) - K - 1

/-- Right-hand side of Cor. C.3; `θ`, `η` are selected values of `𝟙{u ≥ 0}`, `𝟙{v ≥ 0}`. -/
def F (α θ η : ℝ) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![ α / (N : ℝ) * ((exp (z 2) + (N : ℝ) - 2) / D1 N z
        + ∑ j ∈ Finset.range K,
            (exp (z 2) + (N : ℝ) - K - 1 + (j : ℝ) * E z * (1 - θ)) / D2 N K j z
        - (K : ℝ) * E z * θ / D4 N K z),
     α / ((N : ℝ) * ((N : ℝ) - 1)) *
       (∑ j ∈ Finset.range K, (j : ℝ) * E z * θ / D2 N K j z + (K : ℝ) * E z * θ / D4 N K z),
     α / ((N : ℝ) - 1) * ((K : ℝ) * ((N : ℝ) - 1) / D3 N z
        + ((N : ℝ) - K - 1 + (K : ℝ) * E z * (1 - η)) / D4 N K z
        - exp (z 2) / D1 N z
        - ∑ j ∈ Finset.range K, ((j : ℝ) * E z * η + exp (z 2)) / D2 N K j z),
     α / ((N : ℝ) - 1) *
       (∑ j ∈ Finset.range K, (j : ℝ) * E z * η / D2 N K j z + (K : ℝ) * E z * η / D4 N K z) ]

/-- Admissible selections of the indicators at `z`. -/
def Adm (z : Fin 4 → ℝ) (θ η : ℝ) : Prop :=
  θ ∈ Set.Icc (0 : ℝ) 1 ∧ η ∈ Set.Icc (0 : ℝ) 1 ∧
  (0 < u z → θ = 1) ∧ (u z < 0 → θ = 0) ∧ (0 < v z → η = 1) ∧ (v z < 0 → η = 0)

/-- The Filippov velocity set at `z`. -/
def Vel (α : ℝ) (z : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {w | ∃ θ η, Adm z θ η ∧ w = F N K α θ η z}

/-- Filippov solution on `[0, ∞)`, measure-free form: `z` is continuous and at every `t ≥ 0`
the right difference quotients approach the velocity set. -/
def IsSol (α : ℝ) (z : ℝ → Fin 4 → ℝ) : Prop :=
  ContinuousOn z (Set.Ici 0) ∧
  ∀ t ≥ (0 : ℝ), ∀ ε > 0, ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    ∃ w ∈ Vel N K α (z t), ‖h⁻¹ • (z (t + h) - z t) - w‖ < ε

/-- Linear functional `z ↦ ∑ cᵢ zᵢ` (all barrier arguments use such functionals). -/
def lin (c z : Fin 4 → ℝ) : ℝ := c 0 * z 0 + c 1 * z 1 + c 2 * z 2 + c 3 * z 3

/-- The invariant region: `u ≥ 0`, `x₂ ≥ 0`, `y₁ ≥ 0`, `y₂ ≥ 0`. -/
def Good (z : Fin 4 → ℝ) : Prop := 0 ≤ u z ∧ 0 ≤ z 1 ∧ 0 ≤ z 2 ∧ 0 ≤ z 3

/-- Admissible initial state of size at most `R`: in the invariant region and all coordinates
`≤ R` (so `z₀ ∈ [0, R]⁴`). Constants in the theorems depend only on `N`, `K`, `R`. -/
def Init (R : ℝ) (z₀ : Fin 4 → ℝ) : Prop := Good z₀ ∧ ∀ i, z₀ i ≤ R

/-- Coefficients of the averaged variable `X = (x₁ + (N-1) x₂) / N`. -/
def Xc : Fin 4 → ℝ := ![1 / (N : ℝ), ((N : ℝ) - 1) / N, 0, 0]

/-- Sanity check: the components of `F` unfold as expected. -/
example (α θ η : ℝ) (z : Fin 4 → ℝ) :
    F N K α θ η z 3 = α / ((N : ℝ) - 1) *
      (∑ j ∈ Finset.range K, (j : ℝ) * E z * η / D2 N K j z + (K : ℝ) * E z * η / D4 N K z) :=
  rfl

end DFS
