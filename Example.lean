module

public import Init.Meta
import all Parser.Basic
import all Parser.Error
import all Parser.Parser
import all Parser.Prelude
import all Parser.Stream
public import Lemmas

open Lean Lean.Syntax Parser Parser.Char

/- Example for howto transform a partial parser into a total parser -/

/-- -/
abbrev TestParser := SimpleParser String.Slice Char

/-- -/
inductive Ast where
| pure : Char → Ast
| cons : Char → Ast → Ast
deriving Repr

/-- -/
instance : Inhabited Ast where
  default := .pure default

/-- -/
instance : ToString Ast :=
  let rec pp : Ast → String
  | .pure e => toString e
  | .cons e es => toString e ++ " | " ++ pp es
  ⟨pp⟩

/-- -/
def digit : TestParser Char :=
  withErrorMessage "<digit>" do
    tokenMap fun c => if c >= '0' && c <= '9' then some c else none

/-- -/
def bar : TestParser Char :=
  withErrorMessage "<bar>" do
    tokenMap fun c => if c = '|' then some c else none

/-- -/
def digitBar : TestParser Char := do
    let d ← digit
    bar *> return d

namespace Theorems

theorem digitRespectsPositionOnOk (h : digit it = Result.ok s a)
    : Stream.RespectsPosition.respectsPosition Char it s := by
  have : respectsPosition _ _ digit := by simp [digit]
  simp [respectsPosition] at this
  grind [this it (by solve_by_elim)]

theorem digitRespectsPositionOnError (h : digit it = Result.error s e)
    : Stream.RespectsPosition.respectsPosition Char it s := by
  have : respectsPosition _ _ digit := by simp [digit]
  simp [respectsPosition] at this
  grind [this it (by solve_by_elim)]

@[simp] theorem digitBarRespectsPosition
    : respectsPosition _ _ digitBar := by
  simp [digitBar, bind, respectsPosition]
  intro it hv
  split
  · rename_i heq
    split at heq
    · expose_names
      have h2 : Stream.RespectsPosition.respectsPosition Char s rem := by
        have := seqRightRespectsPosition _ _ bar (pure a_1) (by simp [bar]) (by simp)
        simp [respectsPosition] at this
        grind [this s (by assumption)]
      exact Stream.RespectsPosition.isEquivalence.trans (digitRespectsPositionOnOk heq_1) h2
    · simp_all
  · expose_names
    split at heq
    · expose_names
      have h2 : Stream.RespectsPosition.respectsPosition Char s rem := by
        have := seqRightRespectsPosition _ _ bar (pure a_1) (by simp [bar]) (by simp)
        simp [respectsPosition] at this
        grind [this s (by assumption)]
      exact Stream.RespectsPosition.isEquivalence.trans (digitRespectsPositionOnOk heq_1) h2
    · expose_names
      have := digitRespectsPositionOnError heq_1
      simp [pure] at heq
      grind

@[simp] theorem digitBarDecrementsRemainingOnSuccess
    : decrementsRemainingOnSuccess _ _ digitBar := by
  simp [digitBar, bind, decrementsRemainingOnSuccess]
  intro it rem a hv h
  generalize "<ast>: expected digit" = txt at h
  split at h
  · rename_i s a_1 heq
    have h1 : Stream.decrementsRemaining it s := by
      have : decrementsRemainingOnSuccess _ _ digit := by simp [digit]
      simp [decrementsRemainingOnSuccess] at this
      grind
    have h2 : Stream.notIncrementsRemaining s rem := by
      have := seqRightNotIncrementsRemainingOnSuccess _ _ bar (pure a_1) (by simp [bar]) (by simp)
      simp [notIncrementsRemainingOnSuccess] at this
      exact this s rem a (by assumption) (by assumption)
    simp [Stream.decrementsRemaining] at h1
    simp [Stream.notIncrementsRemaining] at h2
    grind [Stream.decrementsRemaining]
  · simp_all

end Theorems

/-- -/
def mkSimpleError (it : String.Slice) (msg : String)
    : Parser.Result (Error.Simple String.Slice Char) String.Slice α :=
  .error it (Error.Simple.addMessage
    (Error.Simple.unexpected it.startInclusive.offset none) it.startInclusive.offset msg)

/-- -/
def run (p : TestParser Ast) (input : String) : IO Unit :=
  match p.run input.toSlice with
  | .ok rem x => IO.println s!"ok {x}, remaining chars {rem.chars.length}"
  | .error rem e => IO.println s!"error {e} at pos {rem.startInclusive.offset}"

namespace Test1

/-- partial function -/
partial def ast : TestParser Ast := do
  let d ← digit
  Ast.cons d <$> (bar *> ast) <|> return Ast.pure d

/--
info: ok 1 | 2, remaining chars 0
-/
#guard_msgs in
#eval run ast "1|2"

end Test1

namespace Test2

open Parser.Stream in
/--
  The recursive function ``loop`` calls ``p`` with a parser that acts like ``p``
  except it fails if called from the same or lower string position

  see https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Advent.20of.20Code.3F/near/405471085
-/
def loop (p : SimpleParser String.Slice Char α → SimpleParser String.Slice Char α)
    : SimpleParser String.Slice Char α := fun it =>
  let p' : SimpleParser String.Slice Char α := fun it' =>
    if Remaining.remaining it' < Remaining.remaining it then
      loop p it'
    else
      return mkSimpleError it' "recursive call going backwards in the string"
  p p' it
termination_by it => Remaining.remaining it

/-- prove termination  at runtime  -/
def ast : TestParser Ast :=
  loop fun p => do
    let d ← digit
    Ast.cons d <$> (bar *> p) <|> return Ast.pure d

/--
info: ok 1 | 2, remaining chars 0
-/
#guard_msgs in
#eval run ast "1|2"

end Test2

namespace Test3

/-- -/
partial def ast : TestParser Ast :=
    (digitBar >>= fun d => ast >>= fun a => pure (Ast.cons d a))
    <|> (do let d ← digit; pure (Ast.pure d))

/--
info: ok 1 | 2 | 3, remaining chars 0
-/
#guard_msgs in
#eval run ast "1|2|3"

end Test3

namespace Test4

open Parser.Stream in
/-- loop corresponds to the following parser:
```
  loop := (do let x ← pre; post x <$> loop) <|> alternative
```
or
```
  loop := (pre >>= fun x => loop >>= fun y => post x y) <|> alternative
```
  with the property ```Parser.decrementsRemainingOnSuccess pre```
  which proves termination
-/
def loop
  (pre : SimpleParser String.Slice Char β)
  (post : β → α → SimpleParser String.Slice Char α)
  (alternative : SimpleParser String.Slice Char α)
  (h : decrementsRemainingOnSuccess _ _ pre)
    : SimpleParser String.Slice Char α := fun it =>
  match hm : pre it with
  | .ok it' b =>
      have := ltRemainingOfDecrementsRemainingOnSuccess pre hm (by solve_by_elim) h
      match loop pre post alternative h it' with
      | .ok it'' a =>
        match post b a it'' with
        | .ok rem a => .ok rem a
        | .error _ _ => alternative it
      | .error _ _ => alternative it
  | .error _ _ => alternative it
termination_by it => Remaining.remaining it

/-- prove termination at compile time  -/
def ast : TestParser Ast :=
    loop
      digitBar (fun d rest => pure (Ast.cons d rest))
      /- <|> -/ (do let d ← digit; pure (Ast.pure d))
      (by simp)

/--
info: ok 1 | 2 | 3, remaining chars 0
-/
#guard_msgs in
#eval run ast "1|2|3"

end Test4
