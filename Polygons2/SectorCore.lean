import Mathlib
set_option maxHeartbeats 4000000
noncomputable section
namespace Polygons2

/-- "ray crosses segment" sign-disjunction. -/
def Disj (x y K : ℚ) : Prop := (0 < x ∧ y < 0 ∧ 0 < K) ∨ (x < 0 ∧ 0 < y ∧ K < 0)

/-- "vertex in the open angular sector between the two rays". -/
def Sect (c1 c2 o : ℚ) : Prop := (0 < o ∧ 0 < c1 ∧ c2 < 0) ∨ (o < 0 ∧ c1 < 0 ∧ 0 < c2)

lemma sector_core (c1a c1b c2a c2b K o : ℚ)
    (ho : o ≠ 0)
    (hR : o * K = c1b * c2a - c1a * c2b)
    (Ha1 : c1a = 0 → 0 < c2a * o)
    (Hb1 : c1b = 0 → 0 < c2b * o)
    (Ha2 : c2a = 0 → c1a * o < 0)
    (Hb2 : c2b = 0 → c1b * o < 0)
    (HK : K = 0 → (0 ≤ c1a * c1b ∧ 0 ≤ c2a * c2b)) :
    (Disj c1a c1b K ↔ Disj c2a c2b K) ↔ (Sect c1a c2a o ↔ Sect c1b c2b o) := by
  unfold Disj Sect
  rcases lt_or_gt_of_ne ho with ho | ho <;>
  rcases lt_trichotomy c1a 0 with h1a | h1a | h1a <;>
  rcases lt_trichotomy c1b 0 with h1b | h1b | h1b <;>
  rcases lt_trichotomy c2a 0 with h2a | h2a | h2a <;>
  rcases lt_trichotomy c2b 0 with h2b | h2b | h2b <;>
  rcases lt_trichotomy K 0 with hK | hK | hK <;>
  (try subst h1a) <;> (try subst h1b) <;> (try subst h2a) <;>
  (try subst h2b) <;> (try subst hK) <;>
  (try replace Ha1 := Ha1 rfl) <;>
  (try replace Hb1 := Hb1 rfl) <;>
  (try replace Ha2 := Ha2 rfl) <;>
  (try replace Hb2 := Hb2 rfl) <;>
  (try replace HK := HK rfl) <;>
  -- Record, for each live variable, the two false sign-atoms. The ones that
  -- cannot hold (would be a false statement) are silently skipped by `try`.
  (try have q1a : ¬ (0 < c1a) := by linarith) <;>
  (try have r1a : ¬ (c1a < 0) := by linarith) <;>
  (try have s1a : c1a ≠ 0 := by intro h; linarith) <;>
  (try have q1b : ¬ (0 < c1b) := by linarith) <;>
  (try have r1b : ¬ (c1b < 0) := by linarith) <;>
  (try have s1b : c1b ≠ 0 := by intro h; linarith) <;>
  (try have q2a : ¬ (0 < c2a) := by linarith) <;>
  (try have r2a : ¬ (c2a < 0) := by linarith) <;>
  (try have s2a : c2a ≠ 0 := by intro h; linarith) <;>
  (try have q2b : ¬ (0 < c2b) := by linarith) <;>
  (try have r2b : ¬ (c2b < 0) := by linarith) <;>
  (try have s2b : c2b ≠ 0 := by intro h; linarith) <;>
  (try have qK : ¬ (0 < K) := by linarith) <;>
  (try have rK : ¬ (K < 0) := by linarith) <;>
  (try have sK : K ≠ 0 := by intro h; linarith) <;>
  (try have qO : ¬ (0 < o) := by linarith) <;>
  (try have rO : ¬ (o < 0) := by linarith) <;>
  first
  | (simp_all only [lt_irrefl, ne_eq, not_true_eq_false, not_false_eq_true, not_not,
        true_and, false_and, and_self, and_true, and_false,
        false_or, or_false, true_or, or_true, iff_self, true_iff, iff_true, iff_false]; done)
  | (exfalso; nlinarith [hR, ho])

end Polygons2
end
