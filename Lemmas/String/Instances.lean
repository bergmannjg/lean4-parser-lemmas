import Init.Meta
import Parser
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Lemmas.Lemmas

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

set_option mvcgen.warning false

namespace Parser.String.Slice

/- see https://github.com/fgdorais/lean4-parser/pull/99, remove when PR#99 is merged
 -/
instance : Parser.Stream.Remaining String.Slice where
  remaining s := s.utf8ByteSize

instance : Parser.Stream.ValidPosition String.Slice where
  valid _ := True
  validOfRemaining it h := by simp

instance : Parser.Stream.AllValid String.Slice where
  valid := by simp [Stream.ValidPosition.valid]

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

private theorem setPositionPrecondition (it : String.Slice) (pos : Stream.Position String.Slice)
  : pos.IsValid it.str ∧ pos ≤ it.endExclusive.offset
    → ∃ rem, Stream.setPosition it pos = rem
              ∧ pos = Parser.Stream.getPosition rem
              ∧ respectsPosition it rem := by
  simp [Stream.setPosition, Stream.getPosition]
  intro h1 h2
  have := slice!PosEq it.str ⟨pos, by grind⟩ ⟨it.endExclusive.offset, it.endExclusive.isValid⟩
            (by simp_all)
  generalize hg : (if h : String.Pos.Raw.IsValid it.str pos
      then it.str.slice! { offset := pos, isValid := by grind } it.endExclusive
      else default) = s
  and_intros
  · split at hg
    · rw [← hg, this.left]
    · simp_all
  · simp_all
  · split at hg
    · rw [← hg, this.right.left]
    · simp_all

/-- no input is consumed if the position is reset after applying a respectful parser -/
private theorem setPositionOfGetPositionEqIfRespectsPosition (s1 s2 : String.Slice) (p)
  (h1 : Stream.getPosition s1 = p) (h2 : respectsPosition s1 s2)
    : Stream.setPosition s2 p = s1 := by
  simp [Stream.getPosition] at h1
  simp [respectsPosition] at h2
  simp [Stream.setPosition]
  have : String.Pos.Raw.IsValid s2.str p := by
    rw [← h1, ← h2.left]
    exact s1.startInclusive.isValid
  split
  · have := slice!PosEq s2.str ⟨p, by grind⟩ ⟨s2.endExclusive.offset, s2.endExclusive.isValid⟩
            (by simp; rw [← h2.right, ← h1]; exact s1.startInclusive_le_endExclusive)
    have := @String.Slice.ext
      (s2.str.slice! { offset := p, isValid := by grind } s2.endExclusive) s1
      (by simp_all)
      (by simp [String.Pos.cast, String.Pos.ext_iff]; simp_all)
      (by simp [String.Pos.cast, String.Pos.ext_iff]; simp_all)
    simp_all
  · simp_all

instance : Stream.RespectsPosition String.Slice Char where
  respectsPosition := respectsPosition
  setPositionOfGetPositionEq s1 s2 p :=
    fun h => setPositionOfGetPositionEqIfRespectsPosition s1 s2 p
  isEquivalence := Equivalence.mk (by simp) (by simp; grind) (by simp; grind)

instance : Stream.SetPositionPrecondition String.Slice Char where
  cond it pos := pos.IsValid it.str ∧ pos ≤ it.endExclusive.offset
  validResult it pos := setPositionPrecondition it pos
  ofGetPosition (s1 s2 : String.Slice) (p : Stream.Position String.Slice) := by
    intro _ h1 h2
    simp [Stream.getPosition] at h1
    simp [Stream.RespectsPosition.respectsPosition] at h2
    and_intros
    · rw [← h1, ← h2.left]
      exact s1.startInclusive.isValid
    · have : p ≤ s2.endExclusive.offset := by
        rw [← h1, ← h2.right]
        exact s1.startInclusive_le_endExclusive
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
      simp_all [Stream.decrementsRemaining]
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
