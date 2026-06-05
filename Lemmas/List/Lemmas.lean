import Init.Meta
import Parser
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Lemmas.Lemmas
import Lemmas.List.Basic

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

set_option mvcgen.warning false

namespace Parser.OfList

@[simp] private def respectsPosition (it rem : (Parser.Stream.OfList τ)) :=
  it.past.reverse ++ it.next = rem.past.reverse ++ rem.next

private theorem getPositionOkEq (it : (Parser.Stream.OfList τ))
  (h : (getPosition : (SimpleParser (Parser.Stream.OfList τ) τ) _) it = Result.ok s a)
    : it = s ∧ it.past.length = a := by
  have hg := getPositionSpec it (by simp)
  simp [wp, Id.run, Stream.getPosition] at hg
  and_intros <;> grind

@[simp] private theorem fwdZeroEq (it : (Stream.OfList τ))
    : (Stream.OfList.setPosition.fwd 0 it) = it := by
  simp [Stream.OfList.setPosition.fwd]

@[simp] private theorem fwdIncrEq (n : Nat)
    : (Stream.OfList.setPosition.fwd (n + 1) ⟨x :: next, past⟩)
      = (Stream.OfList.setPosition.fwd n ⟨next, x :: past⟩) := by
  generalize heq : Stream.OfList.setPosition.fwd n ⟨next, x :: past⟩ = f
  unfold Stream.OfList.setPosition.fwd
  simp_all

theorem fwdTakeReverseEq (it : (Parser.Stream.OfList τ)) (n) (h : n ≤ it.next.length)
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

private theorem fwdNextLengthEq (it : (Parser.Stream.OfList τ)) (n : Nat) (hle : n ≤ it.next.length)
    : (Stream.OfList.setPosition.fwd n it).next.length = it.next.length - n := by
  rw [fwdTakeReverseEq it n hle]
  simp_all +arith

private theorem fwdPastLengthEq (it : (Parser.Stream.OfList τ)) (n : Nat) (hle : n ≤ it.next.length)
    : (Stream.OfList.setPosition.fwd n it).past.length = it.past.length + n := by
  rw [fwdTakeReverseEq it n hle]
  simp_all +arith

@[simp] private theorem revZeroEq (it : (Stream.OfList τ))
    : (Stream.OfList.setPosition.rev 0 it) = it := by
  simp [Stream.OfList.setPosition.rev]

@[simp] private theorem revIncrEq (n : Nat)
    : (Stream.OfList.setPosition.rev (n + 1) ⟨next, x :: past⟩)
      = (Stream.OfList.setPosition.rev n ⟨x :: next, past⟩) := by
  generalize heq : Stream.OfList.setPosition.rev n ⟨x :: next, past⟩ = f
  unfold Stream.OfList.setPosition.rev
  simp_all

theorem revTakeReverseEq (it : (Parser.Stream.OfList τ)) (n) (h : n ≤ it.past.length)
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

private theorem revNextLengthEq (it : (Parser.Stream.OfList τ)) (n : Nat) (hle : n ≤ it.past.length)
    : (Stream.OfList.setPosition.rev n it).next.length = it.next.length + n := by
  rw [revTakeReverseEq it n hle]
  simp_all +arith

private theorem revPastLengthEq (it : (Parser.Stream.OfList τ)) (n : Nat) (hle : n ≤ it.past.length)
    : (Stream.OfList.setPosition.rev n it).past.length = it.past.length - n := by
  rw [revTakeReverseEq it n hle]
  simp_all +arith

private theorem setPositionPrecondition (it : (Parser.Stream.OfList τ))
  (pos : Stream.Position (Parser.Stream.OfList τ))
    : pos ≤ it.past.length + it.next.length
      → ∃ r, (setPosition pos : (SimpleParser (Parser.Stream.OfList τ) τ) Unit) it = r
            ∧ (∃ rem, r = Result.ok rem () ∧ pos = rem.past.length
                        ∧ respectsPosition it rem) := by
  dsimp [setPosition, Stream.setPosition, Stream.OfList.setPosition,
    getStream, setStream, pure, Applicative.toPure, Monad.toApplicative, bind]
  simp_all
  intro h
  split
  · exact ⟨Stream.OfList.setPosition.fwd (pos - it.past.length) it, by
      and_intros
      · rfl
      · rw [fwdPastLengthEq it (pos - it.past.length) (Nat.sub_le_iff_le_add'.mpr h)]
        grind
      · have := fwdTakeReverseEq it (pos - it.past.length) (Nat.sub_le_iff_le_add'.mpr h)
        rw [this]
        simp⟩
  · have hle : pos ≤ it.past.length := by grind
    exact ⟨Stream.OfList.setPosition.rev (it.past.length - pos) it, by
      and_intros
      · rfl
      · rw [revPastLengthEq it (it.past.length - pos) (Nat.sub_le it.past.length pos)]
        grind
      · have := revTakeReverseEq it (it.past.length - pos) (Nat.sub_le it.past.length pos)
        rw [this]
        rw [← List.append_assoc, ← List.reverse_append]
        simp_all⟩

private theorem setPositionEq (it : (Parser.Stream.OfList τ)) (pos)
  (h : (setPosition pos : (SimpleParser (Parser.Stream.OfList τ) τ) Unit) it = Result.ok s ())
  (h : pos ≤ it.past.length + it.next.length)
    : s.past.length = pos ∧ respectsPosition it s := by
  have := setPositionPrecondition it pos h
  grind

/-- no input is consumed if the position is reset after applying a respectful parser -/
private theorem setPositionOfGetPositionEqIfRespectsPosition (s1 s2 s3 s4 : (Parser.Stream.OfList τ) )
  (h1 : (getPosition : (SimpleParser (Parser.Stream.OfList τ) τ) _) s1 = Result.ok s2 p)
  (h2 : respectsPosition s2 s3)
  (h3 : (setPosition p : (SimpleParser (Parser.Stream.OfList τ) τ) Unit) s3 = Result.ok s4 ())
    : s1 = s4 := by
  simp_all
  have := getPositionOkEq s1 h1
  have := setPositionEq s3 p h3 (by
    simp_all
    have : p = s2.past.length := by grind
    rw [this]
    have : (s2.past.reverse ++ s2.next).length = (s3.past.reverse ++ s3.next).length := by grind
    have : s2.past.length + s2.next.length = s3.past.length + s3.next.length := by grind
    rw [← this]
    exact Nat.le_add_right s2.past.length s2.next.length)
  simp [respectsPosition] at this
  have h4 : s2.past.reverse ++ s2.next = s4.past.reverse ++ s4.next := by grind
  have := List.append_inj_left h4 (by grind)
  have := List.append_inj_right h4 (by grind)
  match hm : (s2, s4) with | (⟨s2n, s2p⟩, ⟨s4n, s4p⟩) => simp_all

instance : Stream.RespectsPosition (Parser.Stream.OfList τ) τ where
  respectsPosition := respectsPosition
  setPositionOfGetPositionEq s1 s2 s3 s4 :=
    fun h => setPositionOfGetPositionEqIfRespectsPosition s1 s2 s3 s4
  respectsPositionEq (it) := by simp [respectsPosition]

instance : Stream.SetPositionPrecondition (Parser.Stream.OfList τ) τ where
  cond it pos := pos ≤ it.past.length + it.next.length
  validResult it pos := setPositionPrecondition it pos
  ofGetPosition (s1 s2 s3 : Parser.Stream.OfList τ) (p : Stream.Position (Parser.Stream.OfList τ)) := by
    intro _ h1 h2
    have := getPositionOkEq s1 h1
    simp [Stream.RespectsPosition.respectsPosition] at h2
    simp_all
    have : p = s2.past.length := by grind
    rw [this]
    have : (s2.past.reverse ++ s2.next).length = (s3.past.reverse ++ s3.next).length := by grind
    have : s2.past.length + s2.next.length = s3.past.length + s3.next.length := by grind
    rw [← this]
    exact Nat.le_add_right s2.past.length s2.next.length

private theorem next?SomeOfLt (it : Parser.Stream.OfList τ)
  (h : 0 < Stream.Remaining.remaining it)
    : ∃ rem c, Std.Stream.next? it = some (c, rem) ∧ Stream.decrementsRemaining it rem
                                  ∧ respectsPosition it rem := by
  simp [Stream.Remaining.remaining] at h
  simp [Std.Stream.next?, Stream.Remaining.remaining]
  have : ∃ x next, it = ⟨x :: next, it.past⟩  := by
    have := List.exists_cons_of_length_pos h
    match it with | ⟨_, _⟩ => simp_all
  split <;> simp_all

instance : Stream.Next?OnInput (Parser.Stream.OfList τ) τ where
  cond := next?SomeOfLt

private theorem next?None (it : Parser.Stream.OfList τ) (h : 0 = Stream.Remaining.remaining it)
    : Std.Stream.next? it = none := by
  simp [Stream.Remaining.remaining] at h
  simp [Std.Stream.next?]
  split <;> simp_all

instance : Stream.Next?OnEndOfInput (Parser.Stream.OfList τ) τ where
  cond it _ h := next?None it h
