import Mathlib

/-!
# Combinatorial 1-D flip identity.

Order the crossings of a ray with poly1/poly2 edges by distance (`true` = poly1-crossing,
`false` = poly2-crossing).  A poly1-crossing's point is inside `B` iff an odd number of
poly2-crossings lie beyond it; symmetrically for poly2.  `cseq` sums these "inside"
indicators; the identity says it has the parity of `(#true)·(#false) = N₁·N₂`.
-/

noncomputable section
namespace Polygons2

/-- number of `true` (poly1-crossings). -/
def numTrue (l : List Bool) : ℕ := l.countP id
/-- number of `false` (poly2-crossings). -/
def numFalse (l : List Bool) : ℕ := l.countP (fun b => !b)

/-- Count of crossings whose point is inside the other polygon: a `true` at the head
contributes iff an odd number of `false`s follow, etc. -/
def cseq : List Bool → ℕ
  | [] => 0
  | a :: t => (if a then numFalse t % 2 else numTrue t % 2) + cseq t

@[simp] lemma numTrue_nil : numTrue [] = 0 := rfl
@[simp] lemma numFalse_nil : numFalse [] = 0 := rfl

lemma numTrue_cons (a : Bool) (t : List Bool) :
    numTrue (a :: t) = numTrue t + (if a then 1 else 0) := by
  simp [numTrue, List.countP_cons]

lemma numFalse_cons (a : Bool) (t : List Bool) :
    numFalse (a :: t) = numFalse t + (if a then 0 else 1) := by
  cases a <;> simp [numFalse, List.countP_cons]

/-- The 1-D flip identity: the number of "inside" crossings has the parity of `N₁·N₂`. -/
lemma cseq_parity (l : List Bool) :
    cseq l % 2 = (numTrue l * numFalse l) % 2 := by
  induction l with
  | nil => simp [cseq]
  | cons a t ih =>
    rw [show cseq (a :: t) = (if a then numFalse t % 2 else numTrue t % 2) + cseq t from rfl,
        numTrue_cons, numFalse_cons]
    cases a
    · simp only [if_false, add_zero, if_neg, Bool.false_eq_true]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · simp only [if_true, add_zero]
      rw [Nat.add_mul, Nat.one_mul]
      omega

end Polygons2
end
