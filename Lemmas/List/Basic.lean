import Init.Meta
import Parser

import Lemmas.Basic

open Lean Lean.Syntax Parser Parser.Char

namespace Parser.OfList

/-! Definitions for SimpleParser (OfList τ) τ -/

/- see https://github.com/fgdorais/lean4-parser/pull/99, remove when PR#99 is merged
 -/
instance : Parser.Stream.Remaining (Parser.Stream.OfList τ) where
  remaining s := s.next.length

instance : Parser.Stream.ValidPosition (Parser.Stream.OfList τ)  where
  valid s := True
  validOfRemaining _ _ := by simp
