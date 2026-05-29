import Mathlib
import Polygons2.Geom

/-!
# Sign facts about cross products, from vertex-avoidance.

These supply the hypotheses `Ha1, Ha2, …` consumed by the sector-core algebra.
-/

open Classical
noncomputable section
namespace Polygons2

/-- If `cross d A = 0` and `d ≠ 0` then `A` is a scalar multiple of `d`. -/
lemma parallel_extract {d A : Vector2D} (hd : d ≠ ⟨0, 0⟩) (h : cross d A = 0) :
    ∃ s : ℚ, A.x = s * d.x ∧ A.y = s * d.y := by
  have hc : d.x * A.y - d.y * A.x = 0 := by simpa [cross_def] using h
  by_cases hx : d.x = 0
  · have hy : d.y ≠ 0 := fun hy => hd (by ext <;> simp [hx, hy])
    refine ⟨A.y / d.y, ?_, ?_⟩
    · rw [hx, mul_zero]
      rw [hx] at hc
      have h2 : d.y * A.x = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left hy
    · field_simp
  · refine ⟨A.x / d.x, ?_, ?_⟩
    · field_simp
    · rw [div_mul_eq_mul_div, eq_div_iff hx]; linarith

/-- Key sign fact: if vertex `a` lies on the supporting line of ray `⟨p,d1⟩`
(`cross d1 (a-p) = 0`) but `a` is not on the ray, then `cross d2 (a-p)` has the
same sign as `o = cross d1 d2` (assuming `o ≠ 0`). -/
lemma sign_fact (p d1 d2 a : Vector2D) (hd1 : d1 ≠ ⟨0, 0⟩)
    (ho : cross d1 d2 ≠ 0)
    (ha : a ∉ (Ray.mk p d1 hd1).toSet)
    (hc : cross d1 (vsub a p) = 0) :
    0 < cross d2 (vsub a p) * cross d1 d2 := by
  -- a not on ray, with cross = 0, forces dot < 0
  have hdot : dot d1 (vsub a p) < 0 := by
    by_contra hge
    push_neg at hge
    exact ha ((mem_ray_iff _ a).2 ⟨hc, hge⟩)
  obtain ⟨s, hsx, hsy⟩ := parallel_extract hd1 hc
  -- cross d2 (a-p) = - s * (cross d1 d2);  dot d1 (a-p) = s * (dot d1 d1)
  have hcr : cross d2 (vsub a p) = - s * cross d1 d2 := by
    simp only [cross_def, hsx, hsy]; ring
  have hdt : dot d1 (vsub a p) = s * dot d1 d1 := by
    simp only [dot_def, hsx, hsy]; ring
  have hdd : 0 < dot d1 d1 := dot_pos_of_ne_zero hd1
  have hs : s < 0 := by nlinarith [hdt, hdot, hdd]
  rw [hcr]
  have ho2 : 0 < cross d1 d2 * cross d1 d2 := mul_self_pos.mpr ho
  nlinarith [hs, ho2]

/-- If `p` lies on line `ab` (i.e. `K = 0`) but not on segment `ab`, then for any
direction `d` the cross-products `cross d (a-p)` and `cross d (b-p)` have the same
sign (their product is `≥ 0`). -/
lemma sign_fact_K (p a b d : Vector2D) (hab : a ≠ b)
    (hp : p ∉ (LineSegment.mk a b).toSet)
    (hK : cross (vsub b a) (vsub a p) = 0) :
    0 ≤ cross d (vsub a p) * cross d (vsub b p) := by
  have hba : (vsub b a) ≠ ⟨0, 0⟩ := by
    intro h
    apply hab
    have hx : b.x - a.x = 0 := by have := congrArg Vector2D.x h; simpa [vsub] using this
    have hy : b.y - a.y = 0 := by have := congrArg Vector2D.y h; simpa [vsub] using this
    ext <;> [linarith; linarith]
  obtain ⟨s, hsx, hsy⟩ := parallel_extract hba hK
  -- a - p = s • (b - a)
  set c := cross d (vsub b a) with hc_def
  have hcra : cross d (vsub a p) = s * c := by
    rw [hc_def]; simp only [cross_def]; rw [hsx, hsy]; ring
  have hcrb : cross d (vsub b p) = (1 + s) * c := by
    rw [hc_def]; simp only [cross_def, vsub_x, vsub_y]
    simp only [vsub_x] at hsx; simp only [vsub_y] at hsy
    linear_combination d.x * hsy - d.y * hsx
  -- p ∉ seg forces s(1+s) ≥ 0
  have hmem : (0 ≤ -s ∧ -s ≤ 1) → p ∈ (LineSegment.mk a b).toSet := by
    rintro ⟨h1, h2⟩
    rw [mem_seg_iff']
    refine ⟨-s, h1, h2, ?_, ?_⟩
    · simp only [vsub_x] at hsx; show p.x = a.x + (-s) * (b.x - a.x); linarith
    · simp only [vsub_y] at hsy; show p.y = a.y + (-s) * (b.y - a.y); linarith
  have hs : 0 ≤ s * (1 + s) := by
    by_contra h
    push_neg at h
    have hs1 : -1 < s := by nlinarith
    have hs2 : s < 0 := by nlinarith
    exact hp (hmem ⟨by linarith, by linarith⟩)
  rw [hcra, hcrb]
  nlinarith [hs, mul_self_nonneg c]

end Polygons2
end
