import Init.Meta
import Parser
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Lemmas.Lemmas
import Lemmas.Substring.Basic

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

set_option mvcgen.warning false

namespace Parser.Substring.Raw

@[simp] private def respectsPosition (it rem : Substring.Raw) :=
  it.str = rem.str ∧ it.stopPos = rem.stopPos

private theorem getPositionOkEq (it : Substring.Raw)
  (h : (getPosition : (SimpleParser Substring.Raw Char) _) it = Result.ok s a)
    : it = s ∧ it.startPos = a := by
  have hg := getPositionSpec it (by simp)
  simp [wp, Id.run, Stream.getPosition] at hg
  and_intros <;> grind

private theorem setPositionPrecondition (it : Substring.Raw) (pos :String.Pos.Raw)
  : pos ≤ it.stopPos
    → ∃ r, (setPosition pos : (SimpleParser Substring.Raw Char) Unit) it = r
      ∧ (∃ rem, r = Result.ok rem () ∧ pos = rem.startPos ∧ respectsPosition it rem) := by
  dsimp [setPosition, Stream.setPosition, getStream, setStream, pure,
    Applicative.toPure, Monad.toApplicative, bind]
  intro h
  simp_all
  grind

private theorem setPositionEq (it : Substring.Raw) (pos)
  (h : (setPosition pos : (SimpleParser Substring.Raw Char) Unit) it = Result.ok s ())
  (h : pos ≤ it.stopPos)
    : s.startPos = pos ∧ respectsPosition it s := by
  rw [String.Pos.Raw.ext_iff]
  have := setPositionPrecondition it pos (by solve_by_elim)
  grind

/-- no input is consumed if the position is reset after applying a respectful parser -/
private theorem setPositionOfGetPositionEqIfRespectsPosition (s1 s2 s3 s4 : Substring.Raw )
  (h0 : Stream.ValidPosition.valid s1)
  (h1 : (getPosition : (SimpleParser Substring.Raw  Char) _) s1 = Result.ok s2 p)
  (h2 : respectsPosition s2 s3)
  (h3 : (setPosition p : (SimpleParser Substring.Raw  Char) Unit) s3 = Result.ok s4 ())
    : s1 = s4 := by
  simp_all
  have := getPositionOkEq s1 h1
  have := setPositionEq s3 p h3 (by simp [Stream.ValidPosition.valid] at h0; grind)
  have : s1 = s2 := by grind
  have : s1.str = s4.str := by simp_all
  have : s1.startPos = s4.startPos := by grind
  have : s1.stopPos = s4.stopPos := by simp_all
  cases s1
  cases s4
  grind

instance : Stream.RespectsPosition Substring.Raw Char where
  respectsPosition := respectsPosition
  setPositionOfGetPositionEq := setPositionOfGetPositionEqIfRespectsPosition
  respectsPositionEq (it) := by simp [respectsPosition]

instance : Stream.SetPositionPrecondition Substring.Raw Char where
  cond it pos := pos ≤ it.stopPos
  validResult it pos := setPositionPrecondition it pos
  ofGetPosition (s1 s2 s3 : Substring.Raw) (p : Stream.Position Substring.Raw) := by
    intro h0 h1 h2
    have := getPositionOkEq s1 h1
    simp [Stream.RespectsPosition.respectsPosition] at h2
    simp [Stream.ValidPosition.valid] at h0
    grind

private theorem next?SomeOfLt (it : Substring.Raw)
  (h : 0 < Stream.Remaining.remaining it)
    : ∃ rem c, Std.Stream.next? it = some (c, rem) ∧ Stream.decrementsRemaining it rem
                                  ∧ respectsPosition it rem := by
  simp [Stream.Remaining.remaining, Substring.Raw.bsize] at h
  simp [Std.Stream.next?, Stream.Remaining.remaining, String.Pos.Raw.next]
  exact ⟨{str := it.str,
          startPos := it.startPos + String.Pos.Raw.get it.str it.startPos,
          stopPos := it.stopPos }, by
    and_intros
    · rw [String.Pos.Raw.lt_iff]
      grind
    · rfl
    · simp [HAdd.hAdd, Substring.Raw.bsize]
      have h1 : 0 < (String.Pos.Raw.get it.str it.startPos).utf8Size :=
        Char.utf8Size_pos (String.Pos.Raw.get it.str it.startPos)
      exact Nat.sub_lt_sub_left (by grind) (by grind)
    · rfl
    · rfl⟩

instance : Stream.Next?OnInput Substring.Raw Char where
  cond := next?SomeOfLt

private theorem next?None (it : Substring.Raw ) (h1 : Stream.ValidPosition.valid it)
  (h2 : 0 = Stream.Remaining.remaining it)
    : Std.Stream.next? it = none := by
  simp [Stream.Remaining.remaining, Substring.Raw.bsize] at h2
  simp [Std.Stream.next?, String.Pos.Raw.next]
  simp [Parser.Stream.ValidPosition.valid] at h1
  rw [String.Pos.Raw.le_iff] at h1
  have : it.startPos.byteIdx = it.stopPos.byteIdx := by grind
  rw [String.Pos.Raw.lt_iff]
  grind

instance : Stream.Next?OnEndOfInput Substring.Raw  Char where
  cond := next?None
