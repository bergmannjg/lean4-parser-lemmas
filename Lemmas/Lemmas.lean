module

public import Init.Meta

import all Parser.Basic
import all Parser.Error
import all Parser.Parser
import all Parser.Prelude
import all Parser.Stream

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax

public import Lemmas.Basic
public import Lemmas.Instances

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

@[expose] public section

set_option mvcgen.warning false

namespace Parser

/-! Theorems for SimpleParser σ τ -/

@[grind .] theorem remainingLtOrEq (σ : Type) [Stream.Remaining σ] (it : σ)
    : 0 < Stream.Remaining.remaining it ∨ 0 = Stream.Remaining.remaining it := by
  grind

open Parser.Stream in
theorem ltRemainingOfDecrementsRemainingOnSuccess [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (h : p it = Result.ok it' a)
  (hv : ValidPosition.valid it) (hd : decrementsRemainingOnSuccess _ _ p)
    : Remaining.remaining it' < Remaining.remaining it := by
  simp [decrementsRemainingOnSuccess, decrementsRemaining] at hd
  solve_by_elim

theorem seqRightRespectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (hp : respectsPosition _ _ p) (hq : respectsPosition _ _ q)
      : respectsPosition _ _ (p *> q) := by
  simp [respectsPosition]
  have h : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro it h
  simp [SeqRight.seqRight, bind, pure]
  split
  expose_names
  have hp := hp it
  have hq := hq rem
  · split at heq
    · split at heq
      · expose_names
        simp_all [respectsPosition]
        have hp : Stream.RespectsPosition.respectsPosition τ it s := by simp_all
        exact Stream.RespectsPosition.isEquivalence.trans hp (by grind)
      · expose_names
        have hp : Stream.RespectsPosition.respectsPosition τ it s := by simp_all
        exact Stream.RespectsPosition.isEquivalence.trans hp (by grind)
    · expose_names
      have hp : Stream.RespectsPosition.respectsPosition τ it s := by simp_all
      exact Stream.RespectsPosition.isEquivalence.trans hp (by grind)
  · expose_names
    split at heq
    · split at heq
      · simp_all
      · expose_names
        simp_all [respectsPosition]
        have hp : Stream.RespectsPosition.respectsPosition τ it s := by grind
        exact Stream.RespectsPosition.isEquivalence.trans hp (by grind)
    · expose_names
      have := Result.error.inj heq
      simp_all [respectsPosition]
      have hp : Stream.RespectsPosition.respectsPosition τ it s := by grind
      grind

@[simp] theorem notIncrementsRemainingOnSuccessIfDecrements (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
  (p : SimpleParser σ τ α) (h : decrementsRemainingOnSuccess _ _ p)
      : notIncrementsRemainingOnSuccess _ _ p := by
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining]
  simp [decrementsRemainingOnSuccess, Stream.decrementsRemaining] at h
  grind

theorem seqRightDecrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (hpl : notIncrementsRemainingOnSuccess _ _ p)
  (hqd : decrementsRemainingOnSuccess _ _ q)
      : decrementsRemainingOnSuccess _ _ (p *> q) := by
  simp [decrementsRemainingOnSuccess, Stream.decrementsRemaining]
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining] at hpl
  simp [decrementsRemainingOnSuccess, Stream.decrementsRemaining] at hqd
  have h : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro rem _ _ _
  expose_names
  simp [SeqRight.seqRight, bind, pure]
  split
  · split
    · expose_names
      have := hqd s s_1 a_2 (by grind) heq_1
      grind
    · simp_all
  · simp_all

theorem seqRightNotIncrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (hpl : notIncrementsRemainingOnSuccess _ _ p)
  (hqd : notIncrementsRemainingOnSuccess _ _ q)
      : notIncrementsRemainingOnSuccess _ _ (p *> q) := by
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining]
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining] at hpl
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining] at hqd
  have h : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro rem _ _ _
  expose_names
  simp [SeqRight.seqRight, bind, pure]
  split
  · split
    · expose_names
      have := hqd s s_1 a_2 (by grind) heq_1
      grind
    · simp_all
  · simp_all

@[simp] theorem respectsPositionOfConsumesNoInput (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
  (p : SimpleParser σ τ α) (h : consumesNoInput _ _ p)
      : respectsPosition _ _ p := by
  simp [respectsPosition]
  simp [consumesNoInput] at h
  intro it _
  have h := h it
  simp_all
  exact Stream.RespectsPosition.isEquivalence.refl it

@[simp] theorem pureRespectsPosition (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
      : respectsPosition _ _ (pure a : SimpleParser σ τ α ) := by
  exact respectsPositionOfConsumesNoInput σ τ (pure a) (congrFun rfl)

@[simp] theorem pureNotIncrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
      : notIncrementsRemainingOnSuccess _ _ (pure a : SimpleParser σ τ α) := by
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining]
  intros _
  simp [pure]
  grind

@[simp] theorem orElseRespectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ α)
  (hp : respectsPosition _ _ p) (hq : respectsPosition _ _ q)
      : respectsPosition _ _ (p <|> q) := by
  simp [respectsPosition]
  have h : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro it h
  simp [HOrElse.hOrElse, OrElse.orElse, bind, pure]
  simp [respectsPosition] at hp
  simp [respectsPosition] at hq
  split
  · rename_i heq
    split at heq
    · have := hp it (by grind)
      simp_all
    · rename_i s _ _
      have := Stream.RespectsPosition.setPositionOfGetPositionEq it s (Stream.getPosition it)
                (by grind) rfl (by have := hp it (by grind); simp_all)
      rw [this] at heq
      have := hq it (by grind)
      simp_all
  · rename_i heq
    split at heq
    · simp_all
    · rename_i s _ _
      have := Stream.RespectsPosition.setPositionOfGetPositionEq it s (Stream.getPosition it)
                (by grind) rfl (by have := hp it (by grind); simp_all)
      rw [this] at heq
      have := hq it (by grind)
      simp_all

@[simp] theorem orElseDecrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.AllValid σ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ α) (hpr : respectsPosition _ _ p)
  (hpd : decrementsRemainingOnSuccess _ _ p) (hqd : decrementsRemainingOnSuccess _ _ q)
      : decrementsRemainingOnSuccess _ _ (p <|> q) := by
  simp [decrementsRemainingOnSuccess]
  simp [respectsPosition] at hpr
  simp [decrementsRemainingOnSuccess] at hpd
  simp [decrementsRemainingOnSuccess] at hqd
  have h : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro it rem h1 h2 h3
  simp [HOrElse.hOrElse, OrElse.orElse, bind, pure] at h3
  split at h3
  · grind
  · have := hpr it (by assumption)
    split at this
    · grind
    · expose_names
      exact hqd it rem h1 (by assumption) (by
        have := Stream.RespectsPosition.setPositionOfGetPositionEq it s (Stream.getPosition it)
              (by grind) rfl (by grind)
        rw [this] at h3
        grind)

@[spec] theorem getStreamSpec [Parser.Stream σ τ] (it : σ)
    : ⦃fun s => ⌜s = it⌝⦄
      (getStream : SimpleParser σ τ σ)
      ⦃post⟨fun s s' => ⌜s = it ∧ s' = it⌝, fun _ _ => ⌜False⌝⟩⦄ := by
  mvcgen [getStream]
  simp_all [wp, PredTrans.apply, Parser.run, pure]

@[simp] theorem getStreamEq [Parser.Stream σ τ] (it : σ)
    : (getStream : SimpleParser σ τ _) it = Result.ok it it := by
  simp [getStream, pure]

@[spec] theorem getPositionSpec [Parser.Stream σ τ] (it : σ)
    : ⦃fun s => ⌜s = it⌝⦄
      (getPosition : SimpleParser σ τ (Stream.Position σ))
      ⦃post⟨fun pos s => ⌜s = it ∧ pos = Parser.Stream.getPosition it⌝, fun _ _ => ⌜False⌝⟩⦄ := by
  mvcgen [getPosition] with grind

theorem getPositionEq [Parser.Stream σ τ] (it : σ)
    : (getPosition : SimpleParser σ τ _) it = Result.ok it (Stream.getPosition it) := by
  have hg := getPositionSpec it (by assumption) (by simp)
  simp [wp, PredTrans.apply, Parser.run] at hg
  split at hg <;> grind

@[spec] theorem setStreamSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (it : σ) (pos : Stream.Position σ)
  : ⦃ ⌜Stream.SetPositionPrecondition.cond it pos⌝⦄
    (setStream (Stream.setPosition it pos) : SimpleParser σ τ Unit)
    ⦃post⟨fun _ s => ⌜pos = Parser.Stream.getPosition s
                      ∧ Stream.RespectsPosition.respectsPosition τ it s⌝, fun _ _ => ⌜False⌝⟩⦄ := by
  mvcgen [setStream]
  intros
  simp_all [wp, PredTrans.apply, Parser.run, pure]
  have ⟨r, And.intro hs ⟨rem, hr⟩⟩ := Stream.SetPositionPrecondition.validResult it pos (by grind)
  simp_all

@[spec] theorem setPositionSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (it : σ) (pos : Stream.Position σ)
  : ⦃fun s => ⌜s = it ∧ Stream.SetPositionPrecondition.cond it pos⌝⦄
    (setPosition pos : SimpleParser σ τ Unit)
    ⦃post⟨fun _ s => ⌜pos = Parser.Stream.getPosition s
                      ∧ Stream.RespectsPosition.respectsPosition τ it s⌝, fun _ _ => ⌜False⌝⟩⦄ := by
  mvcgen [setPosition] with grind

theorem setPositionOfGetPositionEq [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.SetPositionPrecondition σ τ] (s1 s2 : σ) (p : Stream.Position σ)
    :  Stream.ValidPosition.valid s1
      → (Parser.getPosition : SimpleParser σ τ (Stream.Position σ)) s1 = Result.ok s1 p
      → Stream.RespectsPosition.respectsPosition τ s1 s2
      → (Parser.setPosition p : SimpleParser σ τ Unit) s2 = Result.ok s1 () := by
  simp [getPosition, setPosition, bind, getStream, setStream, pure,
        Functor.map]
  intro h1 h2 h3
  have h2 := Result.ok.inj h2
  have := Stream.RespectsPosition.setPositionOfGetPositionEq s1 s2 p h1 h2.right h3
  solve_by_elim

/-- setPosition after applying a respectful parser cannot give an error -/
theorem setPositionOfGetPositionFalseIfRespectsPosition  [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.SetPositionPrecondition σ τ]
  (s1 s2 : σ) (p : Stream.Position σ) (e : Error.Simple σ τ)
  (h : (setPosition p : SimpleParser σ τ Unit) s1 = Result.error s2 e)
    : False := by
  simp [setPosition, bind, getStream, setStream] at h

@[simp] theorem throwUnexpectedOfSomeEq [Parser.Stream σ τ]
    (α : Type) (s : σ) (c : τ)
    : (throwUnexpected (some c) s
        : Id (Parser.Result (Error.Simple σ τ) σ α))
      = (Parser.Result.error s (Error.unexpected (Stream.getPosition s) (some c))
        : Id (Parser.Result (Error.Simple σ τ) σ α)) := by
  simp only [throwUnexpected, bind, throw, throwThe, MonadExceptOf.throw, pure]
  have := getPositionEq s
  rfl

@[simp] theorem throwUnexpectedOfNoneEq [Parser.Stream σ τ]
    (α : Type) (s : σ)
    : (throwUnexpected none s
        : Id (Parser.Result (Error.Simple σ τ) σ α))
      = (Parser.Result.error s (Error.unexpected (Stream.getPosition s) none)
        : Id (Parser.Result (Error.Simple σ τ) σ α)) := by
  simp only [throwUnexpected, bind, throw, throwThe, MonadExceptOf.throw, pure]
  have := getPositionEq s
  rfl

@[spec] theorem tokenMapSpec (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ]
  (it : σ) (test : τ → Option α)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it⌝⦄
      ((tokenMap test) : SimpleParser σ τ α)
      ⦃post⟨fun a s => ⌜
              0 < Stream.Remaining.remaining it
              ∧ (∃ c, test c = some a)
              ∧ Stream.decrementsRemaining it s
              ∧ Stream.RespectsPosition.respectsPosition τ it s⌝,
           fun e s => ⌜
              if 0 < Stream.Remaining.remaining it then
                (∃ c p, test c = none ∧ p = Parser.Stream.getPosition s
                        ∧ e = Parser.Error.unexpected p (some c))
                ∧ Stream.decrementsRemaining it s
                ∧ Stream.RespectsPosition.respectsPosition τ it s
              else s = it
                   ∧ e = Parser.Error.unexpected (Stream.getPosition s) none
                   ∧ Stream.RespectsPosition.respectsPosition τ it s⌝⟩⦄ := by
  cases remainingLtOrEq _ it
  · mvcgen [tokenMap]
    simp [wp, tokenCore, Stream.next?, bind, setStream, pure, PredTrans.apply, Parser.run]
    have ⟨rem, ⟨c, hn⟩⟩ := @Stream.Next?OnInput.cond σ τ _ _ _ _ _ it (by grind)
    split
    · rename_i a _
      split
      · simp_all
        cases h : test a.down
        · simp_all
        · grind
      · simp_all
        cases h : test a.down
        · simp_all
          grind
        · simp_all
    · simp_all
  · mvcgen (config := { stepLimit := some 1 }) -- exclude tokenMapSpec
    intros
    dsimp [wp, tokenMap, tokenCore, Stream.next?, bind, getStream, pure,
      PredTrans.pure, PredTrans.apply, throwUnexpected, Id.run, throw, throwThe,
      MonadExceptOf.throw, Parser.run]
    have := @Stream.Next?OnEndOfInput.cond σ τ _ _ _ (by assumption) it (by grind) (by grind)
    simp_all [getPositionEq]
    exact Stream.RespectsPosition.isEquivalence.refl it

@[simp] theorem tokenMapRespectsPosition (σ τ α : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ] (test : τ → Option α)
    : respectsPosition _ _ ((tokenMap test) : SimpleParser σ τ α) := by
  dsimp [respectsPosition]
  intro it s hv heq
  grind [SimpleParser.of_wp_eq (tokenMap test) (tokenMapSpec _ _ it test) it (by grind)]

@[simp] theorem tokenMapDecrementsRemainingOnSuccessOnSuccess (σ τ α : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] (test : τ → Option α)
    : decrementsRemainingOnSuccess _ _ ((tokenMap test) : SimpleParser σ τ α) := by
  dsimp [decrementsRemainingOnSuccess]
  and_intros
  intro it rem _ h1
  grind [SimpleParser.of_wp_eq (tokenMap test) (tokenMapSpec _ _ it test) it (by grind)]

@[spec] theorem anyTokenSpec (σ τ : Type) [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it⌝⦄
      (anyToken : SimpleParser σ τ τ)
      ⦃post⟨fun _ s => ⌜0 < Stream.Remaining.remaining it
                       ∧ Stream.decrementsRemaining it s
                       ∧ Stream.RespectsPosition.respectsPosition τ it s⌝,
           fun _ _ => ⌜0 = Stream.Remaining.remaining it⌝⟩⦄ := by
  simp only [anyToken]
  mintro _
  mspec tokenMapSpec
  · grind
  · simp_all
  · simp_all

@[simp] theorem anyTokenRespectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ]
    : respectsPosition _ _ (anyToken : SimpleParser σ τ τ) := by
  dsimp [respectsPosition, anyToken]
  have := tokenMapRespectsPosition σ τ τ some
  simp [respectsPosition] at this
  grind

@[simp] theorem anyTokenDecrementsRemainingOnSuccessOnSuccess (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
    : decrementsRemainingOnSuccess _ _ (anyToken : SimpleParser σ τ τ) := by
  dsimp [decrementsRemainingOnSuccess, anyToken]
  have := tokenMapDecrementsRemainingOnSuccessOnSuccess σ τ τ some
  simp [decrementsRemainingOnSuccess] at this
  grind

@[spec] theorem lookAheadSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it ∧ respectsPosition _ _ p⌝⦄
      lookAhead p
      ⦃post⟨fun a s => ⌜it = s ∧ ∃ s', p it = Result.ok s' a⌝,
           fun e s => ⌜it = s ∧ ∃ s', p it = Result.error s' e⌝⟩⦄ := by
  mvcgen [lookAhead]
  simp [wp, bind, MonadExceptOf.tryCatch, bind, PredTrans.apply, ParserT.run,  Parser.run,
        throw, throwThe, MonadExceptOf.throw, pure]
  expose_names
  simp [respectsPosition] at h
  split
  · split
    · expose_names
      split at heq
      · expose_names
        split at heq_2
        · expose_names
          grind [setPositionOfGetPositionEq it s_3 (Stream.getPosition it)
                        (by grind) (by simp [getPositionEq]) (by grind)]
        · grind
      · expose_names
        split at heq_2
        · split at heq_2
          · grind
          · expose_names
            grind [setPositionOfGetPositionFalseIfRespectsPosition s_3 s_4]
        · split at heq <;> simp_all
    · grind
  · expose_names
    split at heq
    · simp_all
    · split at heq
      · expose_names
        split at heq_1
        · split at heq_1
          · simp_all
          · expose_names
            grind [setPositionOfGetPositionFalseIfRespectsPosition s_4 s_5]
        · grind [setPositionOfGetPositionEq it s_2 (Stream.getPosition it)
                        (by grind) (by simp [getPositionEq]) (by grind)]
      · expose_names
        grind [setPositionOfGetPositionFalseIfRespectsPosition s_2 s_3]

@[simp] theorem lookAheadConsumesNoInput [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] [Stream.AllValid σ]
  (p : SimpleParser  σ τ α) (hr : respectsPosition σ τ p)
    : consumesNoInput _ _ (lookAhead p) := by
  simp [consumesNoInput]
  intro it
  have := SimpleParser.of_wp_eq (lookAhead p) (lookAheadSpec p it) it (by
    simp_all
    exact Stream.AllValid.valid it)
  grind

@[spec] theorem peekSpec [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  [Stream.SetPositionPrecondition σ τ] (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it⌝⦄
      (peek : SimpleParser σ τ τ)
      ⦃post⟨fun _ s => ⌜s = it ∧ 0 < Stream.Remaining.remaining it⌝,
           fun _ s => ⌜s = it ∧ 0 = Stream.Remaining.remaining it⌝⟩⦄ := by
  cases remainingLtOrEq _ it
  · mvcgen [peek]
    · simp_all
    · grind
    · grind [SimpleParser.of_wp_eq (anyToken) (anyTokenSpec _ _ it) it (by
                simp_all [Stream.ValidPosition.validOfRemaining it (by grind)])]
  · mvcgen [peek]
    · simp_all
    · grind [SimpleParser.of_wp_eq (anyToken) (anyTokenSpec _ _ it) it (by simp_all)]
    · grind

@[spec] theorem withBacktrackingSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it ∧ Parser.respectsPosition _ _ p⌝⦄
      withBacktracking p
      ⦃post⟨fun a s => ⌜p it = .ok s a ∧ Stream.RespectsPosition.respectsPosition τ it s⌝,
           fun e s => ⌜s = it ∧ ∃ s', p it = .error s' e⌝⟩⦄ := by
  mvcgen [withBacktracking]
  simp [wp, bind, MonadExceptOf.tryCatch, bind, PredTrans.apply, ParserT.run, Parser.run,
        throw, throwThe, MonadExceptOf.throw, pure]
  expose_names
  simp [respectsPosition] at h
  split
  · expose_names
    split at heq
    · grind
    · split at heq <;> simp_all
  · expose_names
    split at heq
    · simp_all
    · split at heq
      · expose_names
        grind [setPositionOfGetPositionEq s s_2 r
                  (by grind) (by simp_all [getPositionEq]) (by grind)]
      · expose_names
        grind [setPositionOfGetPositionFalseIfRespectsPosition s_2 s_3]

@[simp] theorem withBacktrackingOfDecrementsRemaining [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.AllValid σ] (p : SimpleParser σ τ α) (h : respectsPosition _ _ p
        ∧ decrementsRemainingOnSuccess _ _ p)
    : decrementsRemainingOnSuccess _ _ (withBacktracking p) := by
  simp [decrementsRemainingOnSuccess]
  intro it
  have := SimpleParser.of_wp_eq (withBacktracking p) (withBacktrackingSpec p it) it (by
            simp_all
            exact Stream.AllValid.valid it)
  simp [respectsPosition, decrementsRemainingOnSuccess] at h
  grind

@[spec] theorem notFollowedBySpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser  σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it ∧ Parser.respectsPosition _ _ p⌝⦄
      notFollowedBy p
      ⦃post⟨fun _ s  => ⌜s = it ∧ ∃ e s', p it = .error s' e⌝,
           fun _ s  => ⌜s = it ∧ ∃ a s', p it = .ok s' a⌝⟩⦄ := by
  mvcgen [notFollowedBy]
  simp only [wp, bind, MonadExceptOf.tryCatch, PredTrans.apply, ParserT.run, Parser.run, pure]
  have := SimpleParser.of_wp_eq (lookAhead p) (lookAheadSpec p it) it (by simp_all)
  simp at this
  simp_all
  grind

@[simp] theorem notFollowedByConsumesNoInput [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] [Stream.AllValid σ]
  (p : SimpleParser  σ τ α) (hr : respectsPosition σ τ p)
    : consumesNoInput _ _ (notFollowedBy p) := by
  simp [consumesNoInput]
  intro it
  have := SimpleParser.of_wp_eq (notFollowedBy p) (notFollowedBySpec p it) it (by
    simp_all
    exact Stream.AllValid.valid it)
  grind

@[spec] theorem endOfInputSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it⌝⦄
      (endOfInput : SimpleParser  σ τ Unit)
      ⦃post⟨fun _ s => ⌜s = it ∧ 0 = Stream.Remaining.remaining s⌝,
           fun _ s => ⌜s = it ∧ 0 < Stream.Remaining.remaining it⌝⟩⦄ := by
  mvcgen [endOfInput]
  simp_all
  all_goals have := SimpleParser.of_wp_eq (anyToken) (anyTokenSpec _ _ it) it (by grind); grind

theorem endOfInputConsumesNoInput [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ] [Stream.AllValid σ]
    : consumesNoInput _ _ (endOfInput : SimpleParser  σ τ Unit) := by
  simp [consumesNoInput]
  intro it
  have := SimpleParser.of_wp_eq endOfInput (endOfInputSpec it) it (by
    simp_all
    exact Stream.AllValid.valid it)
  grind

--      ⦃post⟨fun r => ⌜match p it with
--                     | .ok rem x => r = .ok rem (Sum.inl x)
--                                          ∧ Stream.RespectsPosition.respectsPosition τ it rem
--                     | .error _ e => r = .ok it (Sum.inr e)⌝⟩⦄ := by

@[spec] theorem eoptionSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it ∧ respectsPosition _ _ p⌝⦄
      eoption p
      ⦃post⟨fun a s => ⌜match p it with
                       | .ok rem x => s = rem ∧ a = (Sum.inl x)
                                    ∧ Stream.RespectsPosition.respectsPosition τ it rem
                       | .error rem e => a = Sum.inr e
                                    ∧ Stream.RespectsPosition.respectsPosition τ it rem⌝,
          fun _ _ => ⌜False⌝⟩⦄ := by
  mvcgen [eoption]
  simp [wp, bind, pure, respectsPosition, PredTrans.apply, Parser.run]
  grind

@[spec] theorem optionalSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it ∧ respectsPosition _ _ p⌝⦄
      optional p
      ⦃post⟨fun _ s => ⌜match p it with
                     | .ok rem a => s = rem
                                    ∧ p it = Result.ok rem a
                                    ∧ Stream.RespectsPosition.respectsPosition τ it rem
                     | .error _ _ => True⌝,
          fun _ _ => ⌜False⌝⟩⦄ := by
  mvcgen [optional]
  intros
  have := SimpleParser.of_wp_eq (eoption p) (eoptionSpec p it) it (by simp_all)
  simp [wp, SeqRight.seqRight, PredTrans.apply, Parser.run, bind, pure]
  split
  · split
    · expose_names
      split at heq <;> grind
    · expose_names
      split at heq <;> grind
  · grind

@[spec] theorem withErrorMessageSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (msg : String) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Stream.ValidPosition.valid it ∧ Parser.respectsPosition _ _ p⌝⦄
      withErrorMessage msg p
      ⦃post⟨fun a s => ⌜(∃ rem, p it = .ok rem a ∧ s = rem)
                        ∧ Stream.RespectsPosition.respectsPosition τ it s⌝,
           fun _ s => ⌜Stream.RespectsPosition.respectsPosition τ it s⌝⟩⦄ := by
  mvcgen [withErrorMessage]
  simp [wp, MonadExceptOf.tryCatch, pure,
        bind, throwErrorWithMessage, throw, throwThe, MonadExceptOf.throw, PredTrans.apply,
        Parser.run, ParserT.run]
  expose_names
  simp [respectsPosition] at h
  split
  · expose_names
    split at heq
    · simp_all
      grind
    · simp_all [getPositionEq]
  · expose_names
    split at heq <;> grind [getPositionEq]

@[simp] theorem withErrorMessageRespectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.AllValid σ] (p : SimpleParser σ τ α) (h : respectsPosition _ _ p) (msg : String)
      : respectsPosition _ _ (withErrorMessage msg p) := by
  simp [respectsPosition]
  have h : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro it h
  have := SimpleParser.of_wp_eq (withErrorMessage msg p) (withErrorMessageSpec p msg it) it (by simp_all)
  grind

@[simp] theorem withErrorMessageDecrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.SetPositionPrecondition σ τ]
  [Stream.AllValid σ] (p : SimpleParser σ τ α) (msg : String)
  (h : respectsPosition _ _ p ∧ decrementsRemainingOnSuccess _ _ p)
      : decrementsRemainingOnSuccess _ _ (withErrorMessage msg p) := by
  simp [decrementsRemainingOnSuccess]
  simp [decrementsRemainingOnSuccess] at h
  have : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro it
  have := SimpleParser.of_wp_eq (withErrorMessage msg p) (withErrorMessageSpec p msg it) it (by simp_all)
  grind
