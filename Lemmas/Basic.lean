module

public import Init.Meta
public import Parser

open Lean Lean.Syntax Parser

@[expose] public section

namespace Parser

/-! Definitions for SimpleParser σ τ -/

/-- Returns a natural number measure of remaining input.
  see https://github.com/fgdorais/lean4-parser/pull/99, remove when PR#99 is merged
-/
class Stream.Remaining (σ : Type) where
  /--  natural number measure of remaining input -/
  remaining : σ -> Nat

/-- enables usage of Substring.Raw as σ -/
class Stream.ValidPosition (σ : Type) [Stream.Remaining σ] where
  /-- condition for σ -/
  valid : σ -> Prop
  /- is valid for remaining input -/
  validOfRemaining (it : σ) (h : 0 < Stream.Remaining.remaining it) : valid it

/-- defines streams where Stream.ValidPosition is not necessary -/
class Stream.AllValid (σ : Type) [Stream.Remaining σ] [Stream.ValidPosition σ] where
  valid : ∀ (it : σ), Stream.ValidPosition.valid it

/-- remaining input of ```rem``` is less than remaining input of ```it``` -/
def Stream.decrementsRemaining [Stream.Remaining σ] (it rem : σ)
    := Stream.Remaining.remaining rem < Stream.Remaining.remaining it

/-- remaining input of ```rem``` is less or equal than remaining input of ```it``` -/
def Stream.notIncrementsRemaining [Stream.Remaining σ] (it rem : σ)
    := Stream.Remaining.remaining rem ≤ Stream.Remaining.remaining it

/-- Defines a relation of a stream type that enables the proof of 'no input is consumed'
  with the following steps

* save current position
* aplly a parser that respects the position
* reset to the saved position
 -/
class Stream.RespectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ] where
  /-- respectsPosition relation -/
  r : σ → σ → Prop
  /-- no input is consumed if the position is reset after applying a respectful parser -/
  setPosition_of_getPosition_eq (s1 s2 : σ) (p : Position σ) :
    Stream.ValidPosition.valid s1
    → Stream.getPosition s1 = p
    → r s1 s2
    → Stream.setPosition s2 p = s1
    /-- respectsPosition is a equivalence relation -/
  isEquivalence : Equivalence r

 /-- `Stream.RespectsPosition` relation -/
abbrev Stream.respectsPosition [Parser.Stream σ τ] [Stream.Remaining σ]
    [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] (s1 s2 : σ) : Prop :=
  Stream.RespectsPosition.r τ s1 s2

/-- a parser consumes no input if the corresponding streams are equal -/
def consumesNoInput (σ τ : Type) [Parser.Stream σ τ] (p : SimpleParser σ τ α)
    := ∀ it, (match (p it) with | .ok rem _ => rem | .error rem _ => rem) = it

/-- a parser respects positions if the corresponding streams respect positions -/
def respectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α)
  := ∀ it rem, Stream.ValidPosition.valid it
                → (match (p it) with | .ok rem _ => rem | .error rem _ => rem) = rem
                → Stream.respectsPosition it rem

/-- a parser not increments input on success if the corresponding streams not increment input  -/
def notIncrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] (p : SimpleParser σ τ α)
  := ∀ it rem a, Stream.ValidPosition.valid it → p it = .ok rem a → Stream.notIncrementsRemaining it rem

/-- a parser decrements input on success if the corresponding streams decrement input  -/
def decrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] (p : SimpleParser σ τ α)
  := ∀ it rem a, Stream.ValidPosition.valid it → p it = .ok rem a → Stream.decrementsRemaining it rem

/-- Defines the postcondition of Std.Stream.next? on a non empty stream with class Stream.RespectsPosition
 -/
class Stream.Next?OnInput (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] where
  cond (it : σ) : 0 < Stream.Remaining.remaining it
                  → ∃ rem t, Std.Stream.next? it = some (t, rem)
                                  ∧ Stream.decrementsRemaining it rem
                                  ∧ Stream.respectsPosition it rem

/-- Defines the postcondition of Std.Stream.next? on an empty stream -/
class Stream.Next?OnEndOfInput (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] where
  cond (it : σ) : Stream.ValidPosition.valid it
                  → (0 = Stream.Remaining.remaining it)
                  → Std.Stream.next? it = none

/-- Defines a precondition for Stream.setPosition, so that Parser.setPosition gives a valid result
 -/
class Stream.SetPositionPrecondition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] where
  /-- precondition for Stream.setPosition -/
  cond : σ →  Stream.Position σ → Prop
  /-- Stream.setPosition gives a valid result if ```cond``` is true -/
  valid it pos :
    cond it pos → ∃ rem, Stream.setPosition it pos = rem
                          ∧ pos = Parser.Stream.getPosition rem
                          ∧ Stream.respectsPosition it rem
  /-- Stream.getPosition gives the ```cond``` precondition -/
  of_getPosition s1 s2 p :
    Stream.ValidPosition.valid s1
    → Stream.getPosition s1 = p
    → Stream.respectsPosition s1 s2
    → cond s2 p

/-- example with decrementsRemainingOnSuccess to prove termination -/
def foldr'  (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.AllValid σ] (f : α → β → β) (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (h : decrementsRemainingOnSuccess σ τ p)
    : SimpleParser σ τ β := foldrAux
where
  /-- total recursive function -/
  foldrAux (s : σ) : Id (Parser.Result (Parser.Error.Simple σ τ) σ β) :=
    let savePos := Stream.getPosition s
    match _ : p s with
    | .ok s' x =>
      have : Stream.Remaining.remaining s' < Stream.Remaining.remaining s := by
        simp [decrementsRemainingOnSuccess] at h
        exact h s s' x (Stream.AllValid.valid s) (by grind)
      foldrAux s' >>= fun
      | .ok s'' y => return .ok s'' (f x y)
      | .error s'' e => return .error s'' e
    | .error s' _ => q (Stream.setPosition s' savePos)
  termination_by Stream.Remaining.remaining s
