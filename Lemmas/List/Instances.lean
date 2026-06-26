module

public import Init.Meta

import all Parser.Basic
import all Parser.Error
import all Parser.Parser
import all Parser.Prelude
import all Parser.Stream

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax

public import Lemmas.Lemmas

open Lean Lean.Syntax Parser

open Std.Do

public section

set_option mvcgen.warning false

namespace Parser.OfList

/- see https://github.com/fgdorais/lean4-parser/pull/99, remove when PR#99 is merged
 -/
instance : Parser.Stream.Remaining (Parser.Stream.OfList τ) where
  remaining s := s.next.length

instance : Parser.Stream.ValidPosition (Parser.Stream.OfList τ)  where
  valid s := True
  validOfRemaining _ _ := by simp

instance : Parser.Stream.AllValid (Parser.Stream.OfList τ) where
  valid := by simp [Stream.ValidPosition.valid]

/-- Stream.RespectsPosition -/
@[simp] def respectsPosition (it rem : (Parser.Stream.OfList τ)) :=
  it.past.reverse ++ it.next = rem.past.reverse ++ rem.next

@[simp] private theorem fwd_zero_eq (it : (Stream.OfList τ))
    : (Stream.OfList.setPosition.fwd 0 it) = it := by
  simp [Stream.OfList.setPosition.fwd]

@[simp] private theorem fwd_incr_eq (n : Nat)
    : (Stream.OfList.setPosition.fwd (n + 1) ⟨x :: next, past⟩)
      = (Stream.OfList.setPosition.fwd n ⟨next, x :: past⟩) := by
  generalize heq : Stream.OfList.setPosition.fwd n ⟨next, x :: past⟩ = f
  unfold Stream.OfList.setPosition.fwd
  simp_all

private theorem fwd_take_reverse_eq (it : (Parser.Stream.OfList τ)) (n) (h : n ≤ it.next.length)
    : Stream.OfList.setPosition.fwd n ⟨it.next, it.past⟩
      = ⟨it.next.drop n, (it.next.take n).reverse ++ it.past⟩ := by
  induction n generalizing it
  · simp_all
  · rename_i n h_1
    match heq : it.next with
    | x :: next =>
      have hi := h_1 ⟨next, x :: it.past⟩ (by grind)
      simp [*]
    | [] => simp_all

private theorem fwd_past_length_eq (it : (Parser.Stream.OfList τ)) (n : Nat) (hle : n ≤ it.next.length)
    : (Stream.OfList.setPosition.fwd n it).past.length = it.past.length + n := by
  rw [fwd_take_reverse_eq it n hle]
  simp_all +arith

@[simp] private theorem rev_zero_eq (it : (Stream.OfList τ))
    : (Stream.OfList.setPosition.rev 0 it) = it := by
  simp [Stream.OfList.setPosition.rev]

@[simp] private theorem rev_incr_eq (n : Nat)
    : (Stream.OfList.setPosition.rev (n + 1) ⟨next, x :: past⟩)
      = (Stream.OfList.setPosition.rev n ⟨x :: next, past⟩) := by
  generalize heq : Stream.OfList.setPosition.rev n ⟨x :: next, past⟩ = f
  unfold Stream.OfList.setPosition.rev
  simp_all

private theorem rev_take_reverse_eq (it : (Parser.Stream.OfList τ)) (n) (h : n ≤ it.past.length)
    : Stream.OfList.setPosition.rev n ⟨it.next, it.past⟩
      = ⟨(it.past.take n).reverse ++ it.next, it.past.drop n⟩ := by
  induction n generalizing it
  · simp_all
  · rename_i n h_1
    match heq : it.past with
    | x :: past =>
      have hi := h_1 ⟨x :: it.next, past⟩ (by grind)
      simp [*]
    | [] => simp_all

private theorem rev_past_length_eq (it : (Parser.Stream.OfList τ)) (n : Nat) (hle : n ≤ it.past.length)
    : (Stream.OfList.setPosition.rev n it).past.length = it.past.length - n := by
  rw [rev_take_reverse_eq it n hle]
  simp_all +arith

/-- Stream.SetPositionPrecondition -/
theorem setPosition_precondition (it : (Parser.Stream.OfList τ))
  (pos : Stream.Position (Parser.Stream.OfList τ))
    : pos ≤ it.past.length + it.next.length
      → ∃ rem, Stream.setPosition it pos = rem
              ∧ pos = Parser.Stream.getPosition rem
              ∧ respectsPosition it rem := by
  simp [Stream.setPosition, Stream.getPosition, Stream.OfList.setPosition]
  intro h
  and_intros
  · split
    · rw [fwd_past_length_eq it (pos - it.past.length) (Nat.sub_le_iff_le_add'.mpr h)]
      grind
    · rw [rev_past_length_eq it (it.past.length - pos) (Nat.sub_le it.past.length pos)]
      grind
  · split
    · have := fwd_take_reverse_eq it (pos - it.past.length) (Nat.sub_le_iff_le_add'.mpr h)
      rw [this]
      simp
    · have := rev_take_reverse_eq it (it.past.length - pos) (Nat.sub_le it.past.length pos)
      rw [this]
      rw [← List.append_assoc, ← List.reverse_append]
      simp_all

/-- no input is consumed if the position is reset after applying a respectful parser -/
theorem setPositionOfGetPositionEqIfRespectsPosition (s1 s2 : (Parser.Stream.OfList τ))
  (p) (h1 : Stream.getPosition s1 = p) (h2 : respectsPosition s1 s2)
    : Stream.setPosition s2 p = s1 := by
  have ⟨r, And.intro hr ⟨hg, hs⟩ ⟩ := setPosition_precondition s2 p (by
    simp [Stream.getPosition] at h1
    simp [respectsPosition] at h2
    have : (s2.past.reverse ++ s2.next).length = (s1.past.reverse ++ s1.next).length := by grind      --have : s2.past.length + s2.next.length = s1.past.length + s1.next.length := by grind
    grind)
  rw [hr]

  have : s1.past.length = r.past.length := by
    rw [hg] at h1
    simp [Stream.getPosition] at h1
    assumption

  simp [respectsPosition] at hs
  rw [← h2] at hs
  have := (@List.reverse_inj _ s1.past r.past).mp (List.append_inj_left hs (by grind))
  have := List.append_inj_right hs (by grind)
  cases s1
  cases r
  grind

instance : Stream.RespectsPosition (Parser.Stream.OfList τ) τ where
  r := respectsPosition
  setPosition_of_getPosition_eq s1 s2 p :=
    fun h => setPositionOfGetPositionEqIfRespectsPosition s1 s2 p
  isEquivalence := Equivalence.mk (by simp) (by simp; grind) (by simp; grind)

instance : Stream.SetPositionPrecondition (Parser.Stream.OfList τ) τ where
  cond it pos := pos ≤ it.past.length + it.next.length
  valid it pos := setPosition_precondition it pos
  of_getPosition (s1 s2 : Parser.Stream.OfList τ) (p : Stream.Position (Parser.Stream.OfList τ)) := by
    simp [Stream.ValidPosition.valid, Stream.respectsPosition, Stream.RespectsPosition.r, Stream.getPosition]
    intro h1 h2
    rw [← h1]
    have : (s2.past.reverse ++ s2.next).length = (s1.past.reverse ++ s1.next).length := by grind
    have : s2.past.length + s2.next.length = s1.past.length + s1.next.length := by grind
    rw [this]
    simp

private theorem next?_some (it : Parser.Stream.OfList τ)
  (h : 0 < Stream.Remaining.remaining it)
    : ∃ rem c, Std.Stream.next? it = some (c, rem) ∧ Stream.decrementsRemaining it rem
                                  ∧ respectsPosition it rem := by
  simp [Stream.Remaining.remaining] at h
  simp [Std.Stream.next?, Stream.decrementsRemaining, Stream.Remaining.remaining]
  have : ∃ x next, it = ⟨x :: next, it.past⟩  := by
    have := List.exists_cons_of_length_pos h
    match it with | ⟨_, _⟩ => simp_all
  split <;> simp_all

instance : Stream.Next?OnInput (Parser.Stream.OfList τ) τ where
  cond := next?_some

private theorem next?_none (it : Parser.Stream.OfList τ) (h : 0 = Stream.Remaining.remaining it)
    : Std.Stream.next? it = none := by
  simp [Stream.Remaining.remaining] at h
  simp [Std.Stream.next?]
  split <;> simp_all

instance : Stream.Next?OnEndOfInput (Parser.Stream.OfList τ) τ where
  cond it _ h := next?_none it h
