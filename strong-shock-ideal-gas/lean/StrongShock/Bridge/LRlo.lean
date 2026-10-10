import StrongShock.Basic

namespace StrongShock

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

lemma bridge_LRlo (g s : ℝ) (hg : 0 < g) :
    (let n := 1 + g; let z := 1 / (1 + g); s + Rc g n s z) * ((1 + g) ^ 1 * (1 + g) ^ 2) =
      s * ((1:ℝ) + (5:ℝ) * g + (-3:ℝ) * g * s + (6:ℝ) * g^(2:ℕ) + (-6:ℝ) * g^(2:ℕ) * s + ((3:ℝ)/2) * g^(3:ℕ) + ((-7:ℝ)/2) * g^(3:ℕ) * s + ((-1:ℝ)/2) * g^(4:ℕ) + ((-1:ℝ)/2) * g^(4:ℕ) * s) := by
  simp only [calA, calB, Rc, Cc, P1c, P2c, Kc, K1c, Bc, Lc, c2S, c1S_s, c1S_z, c1S, d1S, V1S, V2S, cS, dS, Vs, As,
    fS, fZ, f0, f1, θ]
  field_simp
  ring


end StrongShock
