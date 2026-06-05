import Init.Meta
import Parser
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Lemmas.Lemmas
import Lemmas.String.Basic

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

set_option mvcgen.warning false

namespace Parser.String.Slice

@[simp] private def respectsPosition (it rem : String.Slice) :=
  it.str = rem.str ∧ it.endExclusive.offset = rem.endExclusive.offset

private theorem slice!PosEq (s : String) (p₁ p₂ : s.Pos) (h : p₁.offset ≤ p₂.offset)
    : (String.slice! s p₁ p₂).startInclusive.offset = p₁.offset
      ∧ (String.slice! s p₁ p₂).endExclusive.offset = p₂.offset
      ∧ (String.slice! s p₁ p₂).str = s := by
  have := @String.Slice.startInclusive_slice (String.toSlice s)
              ⟨p₁.offset, by have := p₁.isValid; simp_all⟩
              ⟨p₂.offset, by have := p₂.isValid; simp_all⟩
              (by assumption)
  have := String.Pos.ext_iff.mp this
  dsimp [String.slice!]
  rw [← @String.Slice.slice_eq_slice! s p₁.toSlice p₂.toSlice h]
  simp

private theorem getPositionOkEq (it : String.Slice)
  (h : (getPosition : (SimpleParser String.Slice Char) _) it = Result.ok s a)
    : it = s ∧ it.startInclusive.offset = a := by
  have hg := getPositionSpec it (by simp)
  simp [wp, Id.run, Stream.getPosition] at hg
  and_intros <;> grind

private theorem setPositionPrecondition (it : String.Slice) (pos : Stream.Position String.Slice)
  : pos.IsValid it.str ∧ pos ≤ it.endExclusive.offset
    → ∃ r, (setPosition pos : (SimpleParser String.Slice Char) Unit) it = r
      ∧ (∃ rem, r = Result.ok rem () ∧ pos = rem.startInclusive.offset
                        ∧ respectsPosition it rem) := by
  dsimp [setPosition, Stream.setPosition, getStream, setStream, pure,
    Applicative.toPure, Monad.toApplicative, bind]
  intro h
  simp_all
  have := slice!PosEq it.str ⟨pos, h.left⟩ ⟨it.endExclusive.offset, it.endExclusive.isValid⟩
            (by simp_all)
  grind

private theorem setPositionEq (it : String.Slice) (pos)
  (h : (setPosition pos : (SimpleParser String.Slice Char) Unit) it = Result.ok s ())
  (hv : String.Pos.Raw.IsValid it.str pos) (hl2 : pos ≤ it.endExclusive.offset)
    : s.startInclusive.offset = pos ∧ respectsPosition it s := by
  rw [String.Pos.Raw.ext_iff]
  have := setPositionPrecondition it pos (by solve_by_elim)
  grind

/-- no input is consumed if the position is reset after applying a respectful parser -/
private theorem setPositionOfGetPositionEqIfRespectsPosition (s1 s2 s3 s4 : String.Slice)
  (h1 : (getPosition : (SimpleParser String.Slice Char) _) s1 = Result.ok s2 p)
  (h2 : respectsPosition s2 s3)
  (h3 : (setPosition p : (SimpleParser String.Slice Char) Unit) s3 = Result.ok s4 ())
    : s1 = s4 := by
  simp_all
  have := getPositionOkEq s1 h1
  have := setPositionEq s3 p h3 (by grind [s1.startInclusive.isValid]) (by
    have : p ≤ s2.endExclusive.offset := by
      rw [this.left] at this
      rw [← this.right]
      exact s2.startInclusive_le_endExclusive
    simp_all)
  have : s1 = s2 := by grind
  have : s1.startInclusive.offset = s4.startInclusive.offset := by grind
  have : s1.endExclusive.offset = s4.endExclusive.offset := by simp_all; grind
  expose_names
  exact @String.Slice.ext s1 s4 (by simp_all)
    (by
      dsimp [String.Pos.cast]; simp_all;
      exact String.Pos.ext_iff.mpr (id (Eq.symm this_2.left)))
    (by dsimp [String.Pos.cast]; simp_all)

instance : Stream.RespectsPosition String.Slice Char where
  respectsPosition := respectsPosition
  setPositionOfGetPositionEq s1 s2 s3 s4 :=
    fun h => setPositionOfGetPositionEqIfRespectsPosition s1 s2 s3 s4
  respectsPositionEq (it) := by simp [respectsPosition]

instance : Stream.SetPositionPrecondition String.Slice Char where
  cond it pos := pos.IsValid it.str ∧ pos ≤ it.endExclusive.offset
  validResult it pos := setPositionPrecondition it pos
  ofGetPosition (s1 s2 s3 : String.Slice) (p : Stream.Position String.Slice) := by
    intro _ h1 h2
    have := getPositionOkEq s1 h1
    simp [Stream.RespectsPosition.respectsPosition] at h2
    and_intros
    · grind [s1.startInclusive.isValid]
    · have : p ≤ s2.endExclusive.offset := by
        rw [this.left] at this
        rw [← this.right]
        exact s2.startInclusive_le_endExclusive
      simp_all

@[simp, grind .] private theorem eqOfRemaining (it : String.Slice)
    : Stream.Remaining.remaining it =  it.endExclusive.offset.byteIdx - it.startInclusive.offset.byteIdx := by
  simp [Stream.Remaining.remaining, String.Slice.utf8ByteSize, String.Pos.Raw.byteDistance]

@[grind .] private theorem ltOfRemaining_iff (it : String.Slice)
    :  0 < Stream.Remaining.remaining it ↔ it.startInclusive.offset < it.endExclusive.offset := by
  simp [Stream.Remaining.remaining, String.Slice.utf8ByteSize, String.Pos.Raw.byteDistance]
  exact Iff.intro
    (fun h => by
      have : it.startInclusive.offset.byteIdx < it.endExclusive.offset.byteIdx := by grind
      assumption)
    (fun h => Nat.zero_lt_sub_of_lt h)

@[grind .] private theorem eqOfRemaining_iff (it : String.Slice)
    :  0 = Stream.Remaining.remaining it ↔ it.startInclusive.offset = it.endExclusive.offset := by
  simp [Stream.Remaining.remaining, String.Slice.utf8ByteSize, String.Pos.Raw.byteDistance]
  exact Iff.intro
    (fun h => by
      have := String.Pos.Raw.le_iff.mp it.startInclusive_le_endExclusive
      have : it.startInclusive.offset.byteIdx = it.endExclusive.offset.byteIdx := by grind
      exact String.Pos.Raw.ext this)
    (fun h => by simp_all)

private theorem startPosNeEndPosOfLt (it : String.Slice)
  (h : it.startInclusive.offset < it.endExclusive.offset)
    : it.startPos != it.endPos := by
  simp [String.Slice.startPos, String.Slice.endPos]
  have : 0 < it.rawEndPos := by
    have := Nat.zero_lt_sub_of_lt h
    assumption
  grind

private theorem startPosEqEndPosOfEq (it : String.Slice)
  (h : it.startInclusive.offset = it.endExclusive.offset)
    : it.startPos = it.endPos := by
  simp [String.Slice.startPos, String.Slice.endPos]
  have : 0 = it.rawEndPos := by
    simp [String.Slice.rawEndPos, String.Slice.utf8ByteSize, String.Pos.Raw.byteDistance]
    simp_all
  grind

private theorem sliceOfNextLt (it : String.Slice) (h : it.startPos ≠ it.endPos)
    : it.startInclusive.offset.byteIdx < (it.startPos.next h).str.offset.byteIdx := by
  simp [String.Slice.Pos.str, String.Slice.Pos.get, String.decodeChar, Char.utf8Size]
  grind

private theorem next?SomeOfLt (it : String.Slice)
  (h : 0 < Stream.Remaining.remaining it)
    : ∃ rem c, Std.Stream.next? it = some (c, rem) ∧ Stream.decrementsRemaining it rem
                                  ∧ respectsPosition it rem := by
  simp [Std.Stream.next?, String.Slice.front?, String.Slice.Pos.get?, String.Slice.drop,
        String.Slice.Pos.nextn, String.Slice.sliceFrom, bind, Option.bind]
  have := startPosNeEndPosOfLt it (by grind)
  simp at this
  split
  · grind
  · expose_names
    split at heq
    · grind
    · have := String.Pos.Raw.lt_iff.mpr (sliceOfNextLt it (by grind))
      simp_all
      have := Char.utf8Size_pos a
      grind

instance : Stream.Next?OnInput String.Slice Char where
  cond := next?SomeOfLt

private theorem next?None (it : String.Slice) (h : 0 = Stream.Remaining.remaining it)
    : Std.Stream.next? it = none := by
  simp [Std.Stream.next?, String.Slice.front?, String.Slice.Pos.get?, String.Slice.drop,
        String.Slice.Pos.nextn, String.Slice.sliceFrom, bind, Option.bind]
  split
  · rfl
  · rename_i heq
    have := startPosEqEndPosOfEq it ((eqOfRemaining_iff it).mp h)
    split at heq <;> simp_all

instance : Stream.Next?OnEndOfInput String.Slice Char where
  cond it _ h := next?None it h
