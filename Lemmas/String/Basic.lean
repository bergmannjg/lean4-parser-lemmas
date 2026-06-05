import Init.Meta
import Parser

import Lemmas.Basic

open Lean Lean.Syntax Parser Parser.Char

namespace Parser.String.Slice

/-! Definitions for SimpleParser String.Slice Char -/

/- see https://github.com/fgdorais/lean4-parser/pull/99, remove when PR#99 is merged
 -/
instance : Parser.Stream.Remaining String.Slice where
  remaining s := s.utf8ByteSize

instance : Parser.Stream.ValidPosition String.Slice where
  valid _ := True
  validOfRemaining it h := by simp
