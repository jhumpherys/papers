import StrongShock.Basic

namespace StrongShock

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

lemma bern_LT1_leaf0 (g k τ s : ℝ) (h0a : (0:ℝ) ≤ g) (h0b : g ≤ (1:ℝ)) :
    0 ≤ (8:ℝ) + (24:ℝ) * g + (-16:ℝ) * g^(3:ℕ) + (-6:ℝ) * g^(4:ℕ) := by
  have u0 : 0 ≤ ((g - (0:ℝ)) * (1:ℝ)) := by linarith
  have w0 : 0 ≤ (((1:ℝ) - g) * (1:ℝ)) := by linarith
  have e : (8:ℝ) + (24:ℝ) * g + (-16:ℝ) * g^(3:ℕ) + (-6:ℝ) * g^(4:ℕ) =
      (8:ℝ) * (((1:ℝ) - g) * (1:ℝ))^(4:ℕ) + (56:ℝ) * ((g - (0:ℝ)) * (1:ℝ))^(1:ℕ) * (((1:ℝ) - g) * (1:ℝ))^(3:ℕ) + (120:ℝ) * ((g - (0:ℝ)) * (1:ℝ))^(2:ℕ) * (((1:ℝ) - g) * (1:ℝ))^(2:ℕ) + (88:ℝ) * ((g - (0:ℝ)) * (1:ℝ))^(3:ℕ) * (((1:ℝ) - g) * (1:ℝ))^(1:ℕ) + (10:ℝ) * ((g - (0:ℝ)) * (1:ℝ))^(4:ℕ) := by ring
  rw [e]
  clear e
  generalize ((g - (0:ℝ)) * (1:ℝ)) = U0 at u0 ⊢
  generalize (((1:ℝ) - g) * (1:ℝ)) = W0 at w0 ⊢
  positivity

lemma bern_LT1 (g k τ s : ℝ) (h0a : (0:ℝ) ≤ g) (h0b : g ≤ (1:ℝ)) :
    0 ≤ (8:ℝ) + (24:ℝ) * g + (-16:ℝ) * g^(3:ℕ) + (-6:ℝ) * g^(4:ℕ) := by
  exact bern_LT1_leaf0 g k τ s (by linarith) (by linarith)

end StrongShock
