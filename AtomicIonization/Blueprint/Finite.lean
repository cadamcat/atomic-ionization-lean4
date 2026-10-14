import Mathlib

/-!
# Uniform bounds over finitely many indices
-/

namespace AtomicIonization.Blueprint

/-- A positive lower bound, uniform over finitely many indices, for a property that weakens as
the bound decreases. -/
lemma finite_lower (f : ℕ → ℝ → Prop) (hmono : ∀ k c c', c' ≤ c → f k c → f k c') :
    ∀ K : ℕ, (∀ k < K, ∃ c : ℝ, 0 < c ∧ f k c) → ∃ c : ℝ, 0 < c ∧ ∀ k < K, f k c
  | 0, _ => ⟨1, one_pos, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | K + 1, h => by
    obtain ⟨c₁, hc₁, h₁⟩ := finite_lower f hmono K (fun k hk => h k (Nat.lt_succ_of_lt hk))
    obtain ⟨c₂, hc₂, h₂⟩ := h K (Nat.lt_succ_self K)
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact hmono k c₁ _ (min_le_left _ _) (h₁ k hk)
    · exact hmono k c₂ _ (min_le_right _ _) h₂

/-- An upper bound, uniform over finitely many indices, for a property that weakens as the bound
increases. -/
lemma finite_upper (f : ℕ → ℝ → Prop) (hmono : ∀ k C C', C ≤ C' → f k C → f k C') :
    ∀ K : ℕ, (∀ k < K, ∃ C : ℝ, f k C) → ∃ C : ℝ, ∀ k < K, f k C
  | 0, _ => ⟨0, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | K + 1, h => by
    obtain ⟨C₁, h₁⟩ := finite_upper f hmono K (fun k hk => h k (Nat.lt_succ_of_lt hk))
    obtain ⟨C₂, h₂⟩ := h K (Nat.lt_succ_self K)
    refine ⟨max C₁ C₂, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact hmono k C₁ _ (le_max_left _ _) (h₁ k hk)
    · exact hmono k C₂ _ (le_max_right _ _) h₂

end AtomicIonization.Blueprint
