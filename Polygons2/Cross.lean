import Mathlib
import Polygons2.Geom
open Classical Set
noncomputable section
namespace Polygons2

lemma crossB_iff (r : Ray) (a b : Vector2D)
    (hp : r.origin ∉ (LineSegment.mk a b).toSet)
    (ha : a ∉ r.toSet) (hb : b ∉ r.toSet) :
    rayIntersectsSegment r ⟨a, b⟩ ↔
      (cross r.direction (vsub a r.origin) > 0 ∧ cross r.direction (vsub b r.origin) < 0
          ∧ cross (vsub b a) (vsub a r.origin) > 0)
      ∨ (cross r.direction (vsub a r.origin) < 0 ∧ cross r.direction (vsub b r.origin) > 0
          ∧ cross (vsub b a) (vsub a r.origin) < 0) := by
  -- abbreviations
  set p := r.origin with hp_def
  set d := r.direction with hd_def
  have hd0 : d ≠ ⟨0, 0⟩ := r.direction_nonzero
  set cA := cross d (vsub a p) with hcA_def
  set cB := cross d (vsub b p) with hcB_def
  set K := cross (vsub b a) (vsub a p) with hK_def
  set D := cA - cB with hD_def
  -- ring identities
  have IDx : K * d.x = D * (a.x - p.x) + cA * (b.x - a.x) := by
    rw [hD_def, hcA_def, hcB_def, hK_def]
    simp only [cross_def, vsub_x, vsub_y]; ring
  have IDy : K * d.y = D * (a.y - p.y) + cA * (b.y - a.y) := by
    rw [hD_def, hcA_def, hcB_def, hK_def]
    simp only [cross_def, vsub_x, vsub_y]; ring
  have hdd_pos : 0 < dot d d := dot_pos_of_ne_zero hd0
  constructor
  · -- (⟹)
    rintro ⟨q, hqr, hqs⟩
    rw [mem_ray_iff] at hqr
    obtain ⟨hq_cross, hq_dot⟩ := hqr
    rw [mem_seg_iff'] at hqs
    obtain ⟨u, hu0, hu1, hqx, hqy⟩ := hqs
    -- p1 = a, p2 = b
    simp only at hqx hqy
    -- Step A: u ≠ 0 and u ≠ 1
    have hu_ne0 : u ≠ 0 := by
      intro hu
      subst hu
      apply ha
      -- q = a, and q ∈ r.toSet
      have hqa : q = a := by
        apply Vector2D.ext
        · rw [hqx]; ring
        · rw [hqy]; ring
      rw [mem_ray_iff]
      rw [← hqa]
      exact ⟨hq_cross, hq_dot⟩
    have hu_ne1 : u ≠ 1 := by
      intro hu
      subst hu
      apply hb
      have hqb : q = b := by
        apply Vector2D.ext
        · rw [hqx]; ring
        · rw [hqy]; ring
      rw [mem_ray_iff]
      rw [← hqb]
      exact ⟨hq_cross, hq_dot⟩
    have hu0' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_ne0)
    have hu1' : u < 1 := lt_of_le_of_ne hu1 hu_ne1
    -- Step B: (1-u)*cA + u*cB = 0
    have hE : (1 - u) * cA + u * cB = 0 := by
      have : cross d (vsub q p) = (1 - u) * cA + u * cB := by
        rw [hcA_def, hcB_def]
        simp only [cross_def, vsub_x, vsub_y, hqx, hqy]; ring
      rw [← this]; exact hq_cross
    -- Step C: cA and cB strictly opposite signs (rule out the all-zero / collinear case)
    have hD_ne : D ≠ 0 := by
      intro hDz
      -- D = 0 means cA = cB, with hE forces cA = cB = 0
      have hcAB : cA = cB := by rw [hD_def] at hDz; linarith
      have hcA0 : cA = 0 := by nlinarith [hE, hu0', hu1']
      have hcB0 : cB = 0 := by rw [hcAB] at hcA0; exact hcA0
      -- Degenerate collinear case: ray is along the line through a, b.
      -- a ∉ ray with cA = 0 forces dot d (a-p) < 0; similarly for b.
      have hdotA_neg : dot d (vsub a p) < 0 := by
        by_contra h
        rw [not_lt] at h
        apply ha
        rw [mem_ray_iff]; exact ⟨hcA0, h⟩
      have hdotB_neg : dot d (vsub b p) < 0 := by
        by_contra h
        rw [not_lt] at h
        apply hb
        rw [mem_ray_iff]; exact ⟨hcB0, h⟩
      -- q on ray: dot d (q-p) ≥ 0
      -- but dot d (q-p) = (1-u)*dot d (a-p) + u*dot d (b-p) < 0
      have hdotq : dot d (vsub q p) = (1 - u) * dot d (vsub a p) + u * dot d (vsub b p) := by
        simp only [dot_def, vsub_x, vsub_y, hqx, hqy]; ring
      rw [hdotq] at hq_dot
      nlinarith [hq_dot, hdotA_neg, hdotB_neg, hu0', hu1']
    -- D ≠ 0, so cA ≠ cB. From hE conclude opposite signs.
    -- cA ≠ 0: if cA = 0 then u*cB = 0 ⇒ cB = 0 ⇒ D = 0, contra.
    have hcA_ne : cA ≠ 0 := by
      intro h
      apply hD_ne
      have hcB0 : cB = 0 := by
        have : u * cB = 0 := by nlinarith [hE, h]
        exact (mul_eq_zero.1 this).resolve_left (ne_of_gt hu0')
      rw [hD_def, h, hcB0]; ring
    have hcB_ne : cB ≠ 0 := by
      intro h
      apply hcA_ne
      have : (1 - u) * cA = 0 := by nlinarith [hE, h]
      exact (mul_eq_zero.1 this).resolve_left (by linarith)
    -- opposite signs: (1-u)cA = -u cB, with 1-u>0, u>0
    have hsigns : (0 < cA ∧ cB < 0) ∨ (cA < 0 ∧ 0 < cB) := by
      rcases lt_or_gt_of_ne hcA_ne with hcAneg | hcApos
      · -- cA < 0; then (1-u)cA < 0, so u cB = -(1-u)cA > 0, so cB > 0
        right
        refine ⟨hcAneg, ?_⟩
        nlinarith [hE, hu0', hu1', hcAneg]
      · left
        refine ⟨hcApos, ?_⟩
        nlinarith [hE, hu0', hu1', hcApos]
    -- Step D: vsub q p = (K/D) • d.  Equivalently q.x-p.x = K*d.x/D, etc.
    -- u = cA / D (from hE: (1-u)cA + u cB = 0 ⟹ cA = u(cA-cB) = u D).
    have hu_eq : u = cA / D := by
      rw [hD_def]
      have hDz' : cA - cB ≠ 0 := by rw [hD_def] at hD_ne; exact hD_ne
      field_simp
      nlinarith [hE]
    -- q.x - p.x = K * d.x / D and q.y - p.y = K * d.y / D
    -- u * D = cA
    have huD : u * D = cA := by
      rw [hu_eq, div_mul_cancel₀]; exact hD_ne
    have hqpx : q.x - p.x = K * d.x / D := by
      rw [eq_div_iff hD_ne, hqx]
      -- (a.x + u*(b.x-a.x) - p.x) * D = K * d.x
      have : (a.x + u * (b.x - a.x) - p.x) * D = D * (a.x - p.x) + (u * D) * (b.x - a.x) := by ring
      rw [this, huD, ← IDx]
    have hqpy : q.y - p.y = K * d.y / D := by
      rw [eq_div_iff hD_ne, hqy]
      have : (a.y + u * (b.y - a.y) - p.y) * D = D * (a.y - p.y) + (u * D) * (b.y - a.y) := by ring
      rw [this, huD, ← IDy]
    -- Step E: dot d (q-p) = (K/D) * dot d d ≥ 0, dot d d > 0, so K/D ≥ 0, so K*D ≥ 0.
    have hdotqp : dot d (vsub q p) = (K / D) * dot d d := by
      simp only [dot_def, vsub_x, vsub_y]
      rw [hqpx, hqpy]; ring
    rw [hdotqp] at hq_dot
    -- Make the abbreviations opaque so the linear arithmetic stays fast.
    set Dd := dot d d with hDd_def
    clear_value cA cB K D Dd
    clear hcA_def hcB_def hK_def hDd_def IDx IDy hdotqp huD hu_eq hE
    -- K/D ≥ 0
    have hKD_nonneg : 0 ≤ K / D := by
      by_contra h
      rw [not_le] at h
      nlinarith [hq_dot, hdd_pos, h]
    -- K*D ≥ 0 (since K/D ≥ 0 and we can't have D=0)
    have hKD : 0 ≤ K * D := by
      rcases lt_or_gt_of_ne hD_ne with hDneg | hDpos
      · -- D < 0, K/D ≥ 0 ⟹ K ≤ 0 ⟹ K*D ≥ 0
        have hKle : K ≤ 0 := by
          by_contra hK
          rw [not_le] at hK
          have : K / D < 0 := div_neg_of_pos_of_neg hK hDneg
          linarith
        nlinarith [hKle, hDneg]
      · have hKge : 0 ≤ K := by
          by_contra hK
          rw [not_le] at hK
          have : K / D < 0 := div_neg_of_neg_of_pos hK hDpos
          linarith
        exact mul_nonneg hKge (le_of_lt hDpos)
    -- Combine: with opposite signs of cA, cB get D's sign and K's sign.
    rcases hsigns with ⟨hcApos, hcBneg⟩ | ⟨hcAneg, hcBpos⟩
    · -- cA > 0, cB < 0, D = cA - cB > 0; K*D ≥ 0 ⟹ K ≥ 0; need K > 0
      left
      have hDpos : 0 < D := by rw [hD_def]; linarith
      have hKge : 0 ≤ K := by
        by_contra hK
        rw [not_le] at hK
        have : K * D < 0 := mul_neg_of_neg_of_pos hK hDpos
        linarith
      -- need K > 0; if K = 0 then q - p = 0, so q = p, p ∈ seg, contradiction
      have hKpos : 0 < K := by
        rcases eq_or_lt_of_le hKge with hK0 | hKpos
        · exfalso
          -- K = 0 ⟹ q = p ⟹ p ∈ seg
          apply hp
          rw [mem_seg_iff']
          refine ⟨u, hu0, hu1, ?_, ?_⟩
          · -- p.x = a.x + u*(b.x - a.x); from hqpx with K=0, q.x = p.x; and hqx
            have hxx : q.x - p.x = 0 := by rw [hqpx, ← hK0]; ring
            have hqpx0 : q.x = p.x := by linarith
            rw [← hqpx0, hqx]
          · have hyy : q.y - p.y = 0 := by rw [hqpy, ← hK0]; ring
            have hqpy0 : q.y = p.y := by linarith
            rw [← hqpy0, hqy]
        · exact hKpos
      exact ⟨hcApos, hcBneg, hKpos⟩
    · -- cA < 0, cB > 0, D = cA - cB < 0; K*D ≥ 0 ⟹ K ≤ 0; need K < 0
      right
      have hDneg : D < 0 := by rw [hD_def]; linarith
      have hKle : K ≤ 0 := by
        by_contra hK
        rw [not_le] at hK
        have : K * D < 0 := mul_neg_of_pos_of_neg hK hDneg
        linarith
      have hKneg : K < 0 := by
        rcases eq_or_lt_of_le hKle with hK0 | hKneg
        · exfalso
          apply hp
          rw [mem_seg_iff']
          refine ⟨u, hu0, hu1, ?_, ?_⟩
          · have hxx : q.x - p.x = 0 := by rw [hqpx, hK0]; ring
            have hqpx0 : q.x = p.x := by linarith
            rw [← hqpx0, hqx]
          · have hyy : q.y - p.y = 0 := by rw [hqpy, hK0]; ring
            have hqpy0 : q.y = p.y := by linarith
            rw [← hqpy0, hqy]
        · exact hKneg
      exact ⟨hcAneg, hcBpos, hKneg⟩
  · -- (⟸)
    intro hdisj
    -- In both cases D ≠ 0; build crossing point q = p + (K/D) d, segment param u = cA/D.
    rcases hdisj with ⟨hcApos, hcBneg, hKpos⟩ | ⟨hcAneg, hcBpos, hKneg⟩
    · -- CASE 1: cA > 0, cB < 0, K > 0, so D = cA - cB > 0
      have hDpos : 0 < D := by rw [hD_def]; linarith
      have hD_ne : D ≠ 0 := ne_of_gt hDpos
      set u := cA / D with hu_def
      set t := K / D with ht_def
      have htge : 0 ≤ t := by rw [ht_def]; exact div_nonneg (le_of_lt hKpos) (le_of_lt hDpos)
      have hu_ge : 0 ≤ u := by rw [hu_def]; exact div_nonneg (le_of_lt hcApos) (le_of_lt hDpos)
      have hu_le : u ≤ 1 := by
        rw [hu_def, div_le_one hDpos, hD_def]; linarith
      have htD : t * D = K := by rw [ht_def, div_mul_cancel₀]; exact hD_ne
      have huD : u * D = cA := by rw [hu_def, div_mul_cancel₀]; exact hD_ne
      -- crossing point
      refine ⟨⟨p.x + t * d.x, p.y + t * d.y⟩, ?_, ?_⟩
      · -- q ∈ r.toSet
        rw [hp_def, hd_def]
        exact ⟨t, htge, rfl, rfl⟩
      · -- q ∈ ⟨a,b⟩.toSet
        rw [mem_seg_iff']
        refine ⟨u, hu_ge, hu_le, ?_, ?_⟩
        · -- p.x + t*d.x = a.x + u*(b.x - a.x)
          show p.x + t * d.x = a.x + u * (b.x - a.x)
          have key : (p.x + t * d.x) * D = (a.x + u * (b.x - a.x)) * D := by
            have e1 : (p.x + t * d.x) * D = p.x * D + (t * D) * d.x := by ring
            have e2 : (a.x + u * (b.x - a.x)) * D = a.x * D + (u * D) * (b.x - a.x) := by ring
            rw [e1, e2, htD, huD, IDx]; ring
          exact mul_right_cancel₀ hD_ne key
        · show p.y + t * d.y = a.y + u * (b.y - a.y)
          have key : (p.y + t * d.y) * D = (a.y + u * (b.y - a.y)) * D := by
            have e1 : (p.y + t * d.y) * D = p.y * D + (t * D) * d.y := by ring
            have e2 : (a.y + u * (b.y - a.y)) * D = a.y * D + (u * D) * (b.y - a.y) := by ring
            rw [e1, e2, htD, huD, IDy]; ring
          exact mul_right_cancel₀ hD_ne key
    · -- CASE 2: cA < 0, cB > 0, K < 0, so D = cA - cB < 0
      have hDneg : D < 0 := by rw [hD_def]; linarith
      have hD_ne : D ≠ 0 := ne_of_lt hDneg
      set u := cA / D with hu_def
      set t := K / D with ht_def
      have htge : 0 ≤ t := by
        rw [ht_def]; exact div_nonneg_of_nonpos (le_of_lt hKneg) (le_of_lt hDneg)
      have hu_ge : 0 ≤ u := by
        rw [hu_def]; exact div_nonneg_of_nonpos (le_of_lt hcAneg) (le_of_lt hDneg)
      have hu_le : u ≤ 1 := by
        rw [hu_def, div_le_one_iff]
        right; right
        refine ⟨hDneg, ?_⟩
        rw [hD_def]; linarith
      have htD : t * D = K := by rw [ht_def, div_mul_cancel₀]; exact hD_ne
      have huD : u * D = cA := by rw [hu_def, div_mul_cancel₀]; exact hD_ne
      refine ⟨⟨p.x + t * d.x, p.y + t * d.y⟩, ?_, ?_⟩
      · rw [hp_def, hd_def]
        exact ⟨t, htge, rfl, rfl⟩
      · rw [mem_seg_iff']
        refine ⟨u, hu_ge, hu_le, ?_, ?_⟩
        · show p.x + t * d.x = a.x + u * (b.x - a.x)
          have key : (p.x + t * d.x) * D = (a.x + u * (b.x - a.x)) * D := by
            have e1 : (p.x + t * d.x) * D = p.x * D + (t * D) * d.x := by ring
            have e2 : (a.x + u * (b.x - a.x)) * D = a.x * D + (u * D) * (b.x - a.x) := by ring
            rw [e1, e2, htD, huD, IDx]; ring
          exact mul_right_cancel₀ hD_ne key
        · show p.y + t * d.y = a.y + u * (b.y - a.y)
          have key : (p.y + t * d.y) * D = (a.y + u * (b.y - a.y)) * D := by
            have e1 : (p.y + t * d.y) * D = p.y * D + (t * D) * d.y := by ring
            have e2 : (a.y + u * (b.y - a.y)) * D = a.y * D + (u * D) * (b.y - a.y) := by ring
            rw [e1, e2, htD, huD, IDy]; ring
          exact mul_right_cancel₀ hD_ne key

end Polygons2
end
