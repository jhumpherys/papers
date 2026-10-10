/-
  Strong ideal-gas shock layers: basic definitions.

  Everything is expressed in the profile coordinates `(s, z)` of the paper:
    V = v_* + a_* s,   a = 1 - V = a_* (1 - s),   z = -V'/(a s),
    c = s (1 - z)/Γ,   d = s z,
  with the profile flow  s' = -s(1-s)z,  z' = f(s,z).
  `g` stands for Γ = γ - 1 and `n` for the transport ratio ν.
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic

namespace StrongShock

noncomputable section

/-- The constant weight `θ = 2/(Γ+2)^2` of (5.1). -/
def θ (g : ℝ) : ℝ := 2 / (g + 2) ^ 2

/-- Downstream specific volume `v_* = Γ/(Γ+2)`. -/
def vstar (g : ℝ) : ℝ := g / (g + 2)
/-- `a_* = 1 - v_* = 2/(Γ+2)`. -/
def astar (g : ℝ) : ℝ := 2 / (g + 2)

/-- Profile specific volume in terms of `s`. -/
def Vs (g s : ℝ) : ℝ := (g + 2 * s) / (g + 2)
/-- Local volume drop `a = 1 - V`. -/
def As (g s : ℝ) : ℝ := 2 * (1 - s) / (g + 2)
/-- Coefficient `c` of the thermal change of variables (4.1). -/
def cS (g s z : ℝ) : ℝ := s * (1 - z) / g
/-- Coefficient `d = a'/a` (4.1). -/
def dS (s z : ℝ) : ℝ := s * z

/-- The polynomials `f₀, f₁` and the slope field `f` of Lemma 2.2. -/
def f0 (g n z : ℝ) : ℝ := z ^ 2 + ((g - 2) / (g + 2) + g / (n * (g + 2))) * z - g / (n * (g + 2))
def f1 (n z : ℝ) : ℝ := -(z - 1) * (z - 1 / n)
def fZ (g n s z : ℝ) : ℝ := (1 - s) * f0 g n z + s * f1 n z
/-- `s' = -s(1-s)z`. -/
def fS (s z : ℝ) : ℝ := -s * (1 - s) * z

/-! Profile derivatives of the coefficients, written as functions of `(s,z)`
    (they are the derivatives along the flow; see `Profile.lean`). -/
/-- `c'` from (4.3). -/
def c1S (g n s z : ℝ) : ℝ := Vs g s * cS g s z / n - dS s z * (As g s + cS g s z)
/-- `d'` from (4.3). -/
def d1S (g n s z : ℝ) : ℝ := -(g + 2) / 2 * As g s * dS s z - g * c1S g n s z
/-- `V' = -a d`. -/
def V1S (g s z : ℝ) : ℝ := -(As g s) * dS s z
/-- `V'' = -a (d^2 + d')`. -/
def V2S (g n s z : ℝ) : ℝ := -(As g s) * (dS s z ^ 2 + d1S g n s z)
/-- partial derivatives of `c1S` in `s` and `z`. -/
def c1S_s (g n s z : ℝ) : ℝ :=
  (2 / (g + 2) * cS g s z + Vs g s * ((1 - z) / g)) / n - z * (As g s + cS g s z)
    - dS s z * (-(2 / (g + 2)) + (1 - z) / g)
def c1S_z (g n s z : ℝ) : ℝ :=
  Vs g s * (-(s / g)) / n - s * (As g s + cS g s z) - dS s z * (-(s / g))
/-- `c''` along the flow (chain rule). -/
def c2S (g n s z : ℝ) : ℝ := c1S_s g n s z * fS s z + c1S_z g n s z * fZ g n s z

/-! Energy coefficients (5.4)–(5.9). -/
def Kc (g n s z : ℝ) : ℝ := (1 - n) * cS g s z / θ g
def K1c (g n s z : ℝ) : ℝ := (1 - n) * c1S g n s z / θ g
def Bc (g n s z : ℝ) : ℝ :=
  (Vs g s * As g s - n * V1S g s z + 2 * n * c1S g n s z - g * cS g s z ^ 2) / θ g
def Lc (g n s z : ℝ) : ℝ :=
  (Vs g s * V1S g s z - n * V2S g n s z + g * cS g s z * V1S g s z
    - (Vs g s + g * cS g s z) * c1S g n s z + n * c2S g n s z) / θ g
def P1c (g n s z : ℝ) : ℝ :=
  (1 - g / 2) * As g s * dS s z + dS s z ^ 2 / 4 + d1S g n s z / 2
def P2c (g n s z : ℝ) : ℝ :=
  (-n * dS s z ^ 2 / 4 + dS s z / 2 + g / 2 * (cS g s z * dS s z - c1S g n s z)) / θ g
def Rc (g n s z : ℝ) : ℝ := K1c g n s z - dS s z * Kc g n s z + Bc g n s z - g
def Cc (g n s z : ℝ) : ℝ :=
  -Kc g n s z * (dS s z ^ 2 / 4 + d1S g n s z / 2) + (Bc g n s z + g) * dS s z / 2 + Lc g n s z

/-- The functions `𝔄`, `𝔅` of (7.5), (7.6), with `q = (1 - z)/Γ`. -/
def calA (g n z : ℝ) : ℝ :=
  (g + 2) * (n + 1) * z ^ 2 / 4 - z + (g + 2) * (n - 1) * (2 - g) * z * ((1 - z) / g) / 8
    + (g + 2) * (n - 1) * g ^ 2 * ((1 - z) / g) ^ 2 / (8 * n)
def calB (g n z : ℝ) : ℝ :=
  g * z / 2 + (g + 2) ^ 2 * (1 - z) / (8 * g)
    * ((3 * n - 1) * z ^ 2 - 2 * (n + 1 - 1 / n) * z + 2 * (1 - 1 / n))

/-- The real quadratic energy density (the integrand of (5.3)) in one real component:
    `p = y'`, `q = y`. -/
def Qform (g n s z p1 p2 q1 q2 : ℝ) : ℝ :=
  p1 ^ 2 + Kc g n s z * p1 * p2 + n / θ g * p2 ^ 2 + Rc g n s z * p1 * q2
    + P1c g n s z * q1 ^ 2 + P2c g n s z * q2 ^ 2 + Cc g n s z * q1 * q2

lemma θ_pos (g : ℝ) (hg : 0 < g) : 0 < θ g := by unfold θ; positivity

/-- The explicit transport region 𝒯 of (1.8). -/
def InT (g n : ℝ) : Prop := 0 < g ∧ g ≤ 2 / 3 ∧ 1 + g / 2 ≤ n ∧ n ≤ 1 + 3 * g / 2

/-- The slope interval of Lemma 2.2. -/
def InSlope (g n z : ℝ) : Prop := min (1 / (g + 1)) (1 / n) ≤ z ∧ z ≤ max (1 / (g + 1)) (1 / n)

end

end StrongShock
