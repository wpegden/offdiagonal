import Tablet.RamseyPropertyStep

-- [TABLET NODE: RamseyPropertyNonempty]

theorem RamseyPropertyNonempty (s k : ℕ) :
    ({n : ℕ | RamseyProperty s k n} : Set ℕ).Nonempty := by
-- BODY
  induction s generalizing k with
  | zero =>
      exact ⟨0, by
        intro G
        left
        exact ⟨∅, by simp⟩⟩
  | succ s ihs =>
      induction k with
      | zero =>
          exact ⟨0, by
            intro G
            right
            exact ⟨∅, by simp⟩⟩
      | succ k ihk =>
          rcases ihs (k + 1) with ⟨a, ha⟩
          rcases ihk with ⟨b, hb⟩
          exact ⟨a + b + 1, RamseyPropertyStep s k a b ha hb⟩
