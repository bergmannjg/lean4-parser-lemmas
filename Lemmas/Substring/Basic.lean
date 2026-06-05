import Init.Meta
import Parser

import Lemmas.Basic

open Lean Lean.Syntax Parser Parser.Char

namespace Parser.Substring.Raw

/-! Definitions for SimpleParser Substring.Raw Char -/

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
