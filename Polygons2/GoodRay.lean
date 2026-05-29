import Mathlib
import Polygons2.Geom
open Classical
noncomputable section
namespace Polygons2

/-- Given a point `p`, two nonzero directions `d1 d2`, and a finite list `V` of points
all distinct from `p`, there is a direction `d3` (with `d3.x = 1`, hence nonzero) that is
not parallel to `d1` or `d2`, and whose forward ray from `p` misses every point of `V`. -/
lemma exists_good_dir (p d1 d2 : Vector2D) (V : List Vector2D)
    (hd1 : d1 ≠ (⟨0, 0⟩ : Vector2D)) (hd2 : d2 ≠ (⟨0, 0⟩ : Vector2D))
    (hpV : ∀ w ∈ V, w ≠ p) :
    ∃ k : ℚ, cross d1 ⟨1, k⟩ ≠ 0 ∧ cross d2 ⟨1, k⟩ ≠ 0 ∧
      ∀ w ∈ V, ¬ ∃ t : ℚ, 0 ≤ t ∧ w.x = p.x + t * 1 ∧ w.y = p.y + t * k := by
  -- The finite set of "bad" slopes to avoid.
  set B : Finset ℚ :=
    insert (d1.y / d1.x)
      (insert (d2.y / d2.x)
        (V.map (fun w => (w.y - p.y) / (w.x - p.x))).toFinset) with hB
  -- Since ℚ is infinite, pick a value not in B.
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset B
  -- Extract the individual avoidance facts from `hk`.
  have hk1 : k ≠ d1.y / d1.x := by
    intro h; exact hk (by rw [hB, h]; exact Finset.mem_insert_self _ _)
  have hk2 : k ≠ d2.y / d2.x := by
    intro h
    refine hk ?_
    rw [hB, h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hkV : ∀ w ∈ V, k ≠ (w.y - p.y) / (w.x - p.x) := by
    intro w hw h
    refine hk ?_
    rw [hB, h]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨w, hw, rfl⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · -- cross d1 ⟨1, k⟩ ≠ 0
    simp only [cross_def]
    rcases eq_or_ne d1.x 0 with hx | hx
    · -- d1.x = 0, so d1.y ≠ 0
      have hy : d1.y ≠ 0 := by
        intro hy; exact hd1 (by ext <;> simp [hx, hy])
      simp [hx]
      exact hy
    · -- d1.x ≠ 0
      intro hcross
      apply hk1
      field_simp
      linarith [hcross]
  · -- cross d2 ⟨1, k⟩ ≠ 0
    simp only [cross_def]
    rcases eq_or_ne d2.x 0 with hx | hx
    · have hy : d2.y ≠ 0 := by
        intro hy; exact hd2 (by ext <;> simp [hx, hy])
      simp [hx]
      exact hy
    · intro hcross
      apply hk2
      field_simp
      linarith [hcross]
  · -- avoidance of every point in V
    rintro w hw ⟨t, ht0, htx, hty⟩
    -- From htx : w.x = p.x + t * 1, get t = w.x - p.x.
    have hteq : t = w.x - p.x := by linarith [htx]
    rcases lt_trichotomy (w.x - p.x) 0 with hsign | hsign | hsign
    · -- w.x - p.x < 0 contradicts t ≥ 0
      rw [hteq] at ht0; linarith
    · -- w.x - p.x = 0 ⟹ w = p, contradiction with hpV
      have hwx : w.x = p.x := by linarith [hsign]
      have ht : t = 0 := by rw [hteq]; linarith [hsign]
      have hwy : w.y = p.y := by rw [hty, ht]; ring
      exact hpV w hw (by ext <;> simp [hwx, hwy])
    · -- w.x - p.x > 0 ⟹ k = (w.y - p.y)/(w.x - p.x), contradiction with hkV
      apply hkV w hw
      rw [hteq] at hty
      -- hty : w.y = p.y + (w.x - p.x) * k
      have hne : w.x - p.x ≠ 0 := ne_of_gt hsign
      field_simp
      linarith [hty]
end Polygons2
end
