import StrongShock.Basic

namespace StrongShock

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

lemma bridge_LT1 (g s : ℝ) (hg : 0 < g) :
    (let n := 1 + g; let z := 1 / (1 + g); 4 * n * θ g - 6 * (n - 1) ^ 2 * (1 - z) ^ 2 / g ^ 2) * ((g + 2) ^ 2 * (1 + g) ^ 2) =
      ((8:ℝ) + (24:ℝ) * g + (-16:ℝ) * g^(3:ℕ) + (-6:ℝ) * g^(4:ℕ)) := by
  simp only [calA, calB, Rc, Cc, P1c, P2c, Kc, K1c, Bc, Lc, c2S, c1S_s, c1S_z, c1S, d1S, V1S, V2S, cS, dS, Vs, As,
    fS, fZ, f0, f1, θ]
  field_simp
  ring


end StrongShock
