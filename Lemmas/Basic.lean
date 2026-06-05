import Init.Meta
import Parser

open Lean Lean.Syntax Parser Parser.Char

namespace Parser

/-! Definitions for SimpleParser σ τ -/

/-- Returns a natural number measure of remaining input.
  see https://github.com/fgdorais/lean4-parser/pull/99, remove when PR#99 is merged
-/
class Stream.Remaining (σ : Type) where
  remaining : σ -> Nat

/-- enables usage of Substring.Raw as σ -/
class Stream.ValidPosition (σ : Type) [Stream.Remaining σ] where
  valid : σ -> Prop
  validOfRemaining (it : σ) (h : 0 < Stream.Remaining.remaining it) : valid it

@[simp] def Stream.decrementsRemaining [Stream.Remaining σ] (it rem : σ)
    := Stream.Remaining.remaining rem < Stream.Remaining.remaining it

/-- Defines a relation of a stream type that enables the proof of 'no input is consumed'
  with the following steps

* save current position
* aplly a parser that respects the position
* reset to the saved position
 -/
class Stream.RespectsPosition (σ τ : Type) [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ] where
  respectsPosition : σ → σ → Prop
  setPositionOfGetPositionEq (s1 s2 s3 s4 : σ) :
    Stream.ValidPosition.valid s1
    → (Parser.getPosition : SimpleParser σ τ (Stream.Position σ)) s1 = Result.ok s2 p
    → respectsPosition s2 s3
    → (Parser.setPosition p : SimpleParser σ τ Unit) s3 = Result.ok s4 ()
    → s1 = s4
  respectsPositionEq (it : σ) : respectsPosition it it

@[simp] def respectsPosition (σ τ : Type) [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α)
  := ∀ it rem, Stream.ValidPosition.valid it
                → (match (p it) with | .ok rem _ => rem | .error rem _ => rem) = rem
                → Stream.RespectsPosition.respectsPosition τ it rem

@[simp] def decrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α)
  := (∀ it rem a, Stream.ValidPosition.valid it
                    → p it = .ok rem a
                    → Stream.decrementsRemaining it rem)
      ∧ respectsPosition σ τ p

/-- Defines the postcondition of Std.Stream.next? on a non empty stream with class Stream.RespectsPosition
 -/
class Stream.Next?OnInput (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] where
  cond (it : σ) : 0 < Stream.Remaining.remaining it
                  → ∃ rem t, Std.Stream.next? it = some (t, rem)
                                  ∧ Stream.decrementsRemaining it rem
                                  ∧ Stream.RespectsPosition.respectsPosition τ it rem

/-- Defines the postcondition of Std.Stream.next? on an empty stream
 -/
class Stream.Next?OnEndOfInput (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] where
  cond (it : σ) : Stream.ValidPosition.valid it
                  → (0 = Stream.Remaining.remaining it)
                  → Std.Stream.next? it = none

/-- Defines a precondition for Parser.setPosition, so that Parser.setPosition gives a valid result
 -/
class Stream.SetPositionPrecondition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] where
  cond : σ →  Stream.Position σ → Prop
  validResult it pos : cond it pos → ∃ r, (Parser.setPosition pos : SimpleParser σ τ Unit) it = r
                      ∧ (∃ rem, r = Result.ok rem () ∧ pos = Parser.Stream.getPosition rem
                                  ∧ Stream.RespectsPosition.respectsPosition τ it rem)
  ofGetPosition (s1 s2 s3 : σ) (p : Stream.Position σ) :
    Stream.ValidPosition.valid s1
    → (Parser.getPosition : SimpleParser σ τ (Stream.Position σ)) s1 = Result.ok s2 p
    → Stream.RespectsPosition.respectsPosition τ s2 s3
    → cond s3 p

/-- example with decrementsRemainingOnSuccess to prove termination -/
def foldr'  (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] (f : α → β → β) (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (h : decrementsRemainingOnSuccess σ τ p) (hAll : ∀ (it : σ), Stream.ValidPosition.valid it)
    : SimpleParser σ τ β := fun s => foldrAux s
where
  foldrAux (s : σ) : Id (Parser.Result (Parser.Error.Simple σ τ) σ β) :=
    let savePos := Stream.getPosition s
    match _: p s with
    | .ok s' x =>
      have : Stream.Remaining.remaining s' < Stream.Remaining.remaining s := by
        simp [decrementsRemainingOnSuccess] at h
        exact h.left s s' x (hAll s) (by grind)
      foldrAux s' >>= fun
      | .ok s'' y => return .ok s'' (f x y)
      | .error s'' e => return .error s'' e
    | .error s' _ => q (Stream.setPosition s' savePos)
  termination_by Stream.Remaining.remaining s
