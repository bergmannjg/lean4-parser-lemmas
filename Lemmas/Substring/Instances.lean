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

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

public section

set_option mvcgen.warning false

namespace Parser.Substring.Raw

/- see https://github.com/fgdorais/lean4-parser/pull/99, remove when PR#99 is merged
 -/
instance : Parser.Stream.Remaining Substring.Raw where
  remaining s := s.bsize

instance : Parser.Stream.ValidPosition Substring.Raw where
  valid s := s.startPos ≤ s.stopPos
  validOfRemaining it h := by
    simp [Stream.Remaining.remaining, Substring.Raw.bsize] at h
    rw [String.Pos.Raw.le_iff]
    grind

/-- Stream.RespectsPosition -/
@[simp] def respectsPosition (it rem : Substring.Raw) :=
  it.str = rem.str ∧ it.stopPos = rem.stopPos

/-- Stream.SetPositionPrecondition -/
theorem setPositionPrecondition (it : Substring.Raw) (pos :String.Pos.Raw)
  : pos ≤ it.stopPos
    → ∃ rem, Stream.setPosition it pos = rem
                          ∧ pos = Parser.Stream.getPosition rem
                          ∧ respectsPosition it rem := by
  dsimp [setPosition, Stream.setPosition, getStream, setStream, pure,
    Applicative.toPure, Monad.toApplicative, bind]
  intro h
  simp_all
  grind

/-- no input is consumed if the position is reset after applying a respectful parser -/
theorem setPositionOfGetPositionEqIfRespectsPosition (s1 s2 : Substring.Raw ) (p)
  (h0 : Stream.ValidPosition.valid s1)
  (h1 : Stream.getPosition s1 = p) (h2 : respectsPosition s1 s2)
    : Stream.setPosition s2 p = s1 := by
  simp [Stream.ValidPosition.valid] at h0
  simp [Stream.getPosition] at h1
  simp [respectsPosition] at h2
  simp [Stream.setPosition]
  simp_all
  generalize h : ({ str := s2.str, startPos := p, stopPos := s2.stopPos } : Substring.Raw) = rem
  have : s1.str = rem.str := by grind
  have : s1.startPos = rem.startPos := by grind
  have : s1.stopPos = rem.stopPos := by grind
  cases s1
  cases rem
  grind

instance : Stream.RespectsPosition Substring.Raw Char where
  respectsPosition := respectsPosition
  setPositionOfGetPositionEq := setPositionOfGetPositionEqIfRespectsPosition
  isEquivalence := Equivalence.mk (by simp) (by simp; grind) (by simp; grind)

instance : Stream.SetPositionPrecondition Substring.Raw Char where
  cond it pos := pos ≤ it.stopPos
  validResult it pos := setPositionPrecondition it pos
  ofGetPosition (s1 s2 : Substring.Raw) (p : Stream.Position Substring.Raw) := by
    simp [Stream.ValidPosition.valid, Stream.getPosition,
          Stream.RespectsPosition.respectsPosition]
    intros
    simp_all

private theorem next?SomeOfLt (it : Substring.Raw)
  (h : 0 < Stream.Remaining.remaining it)
    : ∃ rem c, Std.Stream.next? it = some (c, rem) ∧ Stream.decrementsRemaining it rem
                                  ∧ respectsPosition it rem := by
  simp [Stream.Remaining.remaining, Substring.Raw.bsize] at h
  simp [Std.Stream.next?, String.Pos.Raw.next]
  exact ⟨{str := it.str,
          startPos := it.startPos + String.Pos.Raw.get it.str it.startPos,
          stopPos := it.stopPos }, by
    and_intros
    · rw [String.Pos.Raw.lt_iff]
      grind
    · rfl
    · simp [HAdd.hAdd]
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
