module

public import Init.Meta

import all Parser.Basic
import all Parser.Error
import all Parser.Parser
import all Parser.Char.Basic
import all Parser.Prelude
import all Parser.Stream

public import Std.Tactic.Do
public import Std.Tactic.Do.Syntax

public import Lemmas.Basic
public import Lemmas.Instances
public import Lemmas.SimpLemmas

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

@[expose] public section

set_option mvcgen.warning false

namespace Parser

/-! Theorems for SimpleParser σ τ -/

@[grind .] private theorem Remaining.lt_or_eq (σ : Type) [Stream.Remaining σ] (it : σ)
    : 0 < Stream.Remaining.remaining it ∨ 0 = Stream.Remaining.remaining it := by
  grind

open Parser.Stream in
theorem Remaining.lt_of_decrementsRemainingOnSuccess [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (h : p it = Result.ok it' a)
  (hd : decrementsRemainingOnSuccess _ _ p)
    : Remaining.remaining it' < Remaining.remaining it := by
  simp [decrementsRemainingOnSuccess, decrementsRemaining] at hd
  solve_by_elim

@[simp, grind .] theorem respectsPosition_refl (σ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] (it : σ)
    : Stream.respectsPosition it it :=
  Stream.RespectsPosition.isEquivalence.refl it

@[grind .] theorem respectsPosition_trans (σ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
   [Stream.RespectsPosition σ τ] (s1 s2 s3 : σ)
  : Stream.respectsPosition s1 s2
    → Stream.respectsPosition s2 s3
    → Stream.respectsPosition s1 s3 := by
  intro h1 h2
  exact Stream.RespectsPosition.isEquivalence.trans h1 h2

theorem respectsPosition_seqRight (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (hp : respectsPosition _ _ p) (hq : respectsPosition _ _ q)
      : respectsPosition _ _ (p *> q) := by
  simp [respectsPosition]
  intro it
  simp [SeqRight.seqRight, bind, pure]
  split
  rename_i rem _ heq
  have hp := hp it
  have hq := hq rem
  simp_all [respectsPosition]
  split at heq
  · split at heq <;> grind
  · grind
  simp_all [respectsPosition]
  rename_i heq
  split at heq
  · split at heq <;> grind
  · grind

@[simp] theorem notIncrementsRemainingOnSuccess_of_decrementsRemaining (σ τ : Type)
  [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (h : decrementsRemainingOnSuccess _ _ p)
      : notIncrementsRemainingOnSuccess _ _ p := by
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining]
  simp [decrementsRemainingOnSuccess, Stream.decrementsRemaining] at h
  grind

theorem decrementsRemainingOnSuccess_seqRight (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (hpl : notIncrementsRemainingOnSuccess _ _ p)
  (hqd : decrementsRemainingOnSuccess _ _ q)
      : decrementsRemainingOnSuccess _ _ (p *> q) := by
  simp [decrementsRemainingOnSuccess, Stream.decrementsRemaining]
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining] at hpl
  simp [decrementsRemainingOnSuccess, Stream.decrementsRemaining] at hqd
  intro rem _ _
  expose_names
  simp [SeqRight.seqRight, bind, pure]
  split
  · split
    · expose_names
      have := hqd s s_1 a_2 (by grind)
      grind
    · simp_all
  · simp_all

theorem notIncrementsRemainingOnSuccess_seqRight (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  (hpl : notIncrementsRemainingOnSuccess _ _ p)
  (hqd : notIncrementsRemainingOnSuccess _ _ q)
      : notIncrementsRemainingOnSuccess _ _ (p *> q) := by
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining]
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining] at hpl
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining] at hqd
  intro rem _ _
  expose_names
  simp [SeqRight.seqRight, bind, pure]
  split
  · split
    · expose_names
      have := hqd s s_1 a_2 (by grind)
      grind
    · simp_all
  · simp_all

@[simp] theorem respectsPosition_of_consumesNoInput (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (h : consumesNoInput _ _ p)
      : respectsPosition _ _ p := by
  simp [respectsPosition]
  simp [consumesNoInput] at h
  intro it
  have h := h it
  simp_all

@[simp] theorem respectsPosition_pure (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ]
      : respectsPosition _ _ (pure a : SimpleParser σ τ α ) := by
  exact respectsPosition_of_consumesNoInput σ τ (pure a) (congrFun rfl)

@[simp] theorem notIncrementsRemainingOnSuccess_pure (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ]
      : notIncrementsRemainingOnSuccess _ _ (pure a : SimpleParser σ τ α) := by
  simp [notIncrementsRemainingOnSuccess, Stream.notIncrementsRemaining]
  intros _
  simp [pure]
  grind

@[simp] theorem respectsPosition_orElse (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ α)
  (hp : respectsPosition _ _ p) (hq : respectsPosition _ _ q)
      : respectsPosition _ _ (p <|> q) := by
  simp [respectsPosition]
  intro it
  simp [HOrElse.hOrElse, OrElse.orElse, bind, pure]
  simp [respectsPosition] at hp
  simp [respectsPosition] at hq
  split
  · rename_i heq
    split at heq
    · have := hp it
      simp_all
    · rename_i s _ _
      have := Stream.RespectsPosition.setPosition_of_getPosition_eq it s (Stream.getPosition it)
                (by grind) (by grind)
      rw [this] at heq
      have := hq it
      simp_all
  · rename_i heq
    split at heq
    · simp_all
    · rename_i s _ _
      have := Stream.RespectsPosition.setPosition_of_getPosition_eq it s (Stream.getPosition it)
                (by grind) (by grind)
      rw [this] at heq
      have := hq it
      simp_all

@[simp] theorem dDecrementsRemainingOnSuccess_orElse (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ α) (hpr : respectsPosition _ _ p)
  (hpd : decrementsRemainingOnSuccess _ _ p) (hqd : decrementsRemainingOnSuccess _ _ q)
      : decrementsRemainingOnSuccess _ _ (p <|> q) := by
  simp [decrementsRemainingOnSuccess]
  simp [respectsPosition] at hpr
  simp [decrementsRemainingOnSuccess] at hpd
  simp [decrementsRemainingOnSuccess] at hqd
  intro it rem a h
  simp [HOrElse.hOrElse, OrElse.orElse, bind, pure] at h
  split at h
  · grind
  · have := hpr it
    split at this
    · grind
    · expose_names
      exact hqd it rem a (by
        have := Stream.RespectsPosition.setPosition_of_getPosition_eq it s (Stream.getPosition it)
              (by grind) (by grind)
        rw [this] at h
        grind)

@[spec] theorem Spec.getStream [Parser.Stream σ τ] (it : σ)
    : ⦃fun s => ⌜s = it⌝⦄
      (Parser.getStream : SimpleParser σ τ σ)
      ⦃⇓ s s' => ⌜s = it ∧ s' = it⌝⦄ := by
  mvcgen [Parser.getStream]
  simp_all [wp, PredTrans.apply, Parser.run, pure]

@[simp] theorem getStream_eq_ok [Parser.Stream σ τ] (it : σ)
    : (getStream : SimpleParser σ τ _) it = Result.ok it it := by
  simp [getStream, pure]

@[spec] theorem Spec.getPosition [Parser.Stream σ τ] (it : σ)
    : ⦃fun s => ⌜s = it⌝⦄
      (Parser.getPosition : SimpleParser σ τ (Stream.Position σ))
      ⦃⇓ pos s => ⌜s = it ∧ pos = Parser.Stream.getPosition it⌝⦄ := by
  mvcgen [Parser.getPosition] with grind

@[spec] theorem Spec.setStream [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (it : σ) (pos : Stream.Position σ)
  : ⦃ ⌜Stream.SetPositionPrecondition.cond it pos⌝⦄
    (Parser.setStream (Stream.setPosition it pos) : SimpleParser σ τ Unit)
    ⦃⇓ _ s => ⌜pos = Parser.Stream.getPosition s
               ∧ Stream.respectsPosition it s⌝⦄ := by
  mvcgen [Parser.setStream]
  intros
  simp_all [wp, PredTrans.apply, Parser.run, pure]
  have ⟨r, And.intro hs ⟨rem, hr⟩⟩ := Stream.SetPositionPrecondition.valid it pos (by grind)
  simp_all

@[spec] theorem Spec.setPosition [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (it : σ) (pos : Stream.Position σ)
  : ⦃fun s => ⌜s = it ∧ Stream.SetPositionPrecondition.cond it pos⌝⦄
    (Parser.setPosition pos : SimpleParser σ τ Unit)
    ⦃⇓ _ s => ⌜pos = Parser.Stream.getPosition s
                      ∧ Stream.respectsPosition it s⌝⦄ := by
  mvcgen [Parser.setPosition] with grind

theorem setPosition_of_getPosition_eq [Parser.Stream σ τ]
  [Stream.Remaining σ]  [Stream.RespectsPosition σ τ]
  (s1 s2 : σ) (p : Stream.Position σ)
    :  (Parser.getPosition : SimpleParser σ τ (Stream.Position σ)) s1 = Result.ok s1 p
      → Stream.respectsPosition s1 s2
      → (Parser.setPosition p : SimpleParser σ τ Unit) s2 = Result.ok s1 () := by
  simp [getPosition, setPosition, bind, getStream, setStream, pure,
        Functor.map]
  intro h1 h2
  have h2 := Result.ok.inj h1
  have := Stream.RespectsPosition.setPosition_of_getPosition_eq s1 s2 p h2.right
  solve_by_elim

@[spec] theorem Spec.tokenMap (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  (it : σ) (test : τ → Option α)
    : ⦃fun s => ⌜s = it⌝⦄
      ((Parser.tokenMap test) : SimpleParser σ τ α)
      ⦃post⟨fun a s =>
              ⌜0 < Stream.Remaining.remaining it
              ∧ (∃ c, Stream.next? it = some (c, s) ∧ test c = some a)
              ∧ Stream.decrementsRemaining it s
              ∧ Stream.respectsPosition it s⌝,
           fun e s =>
              ⌜if 0 < Stream.Remaining.remaining it then
                 (∃ c, Stream.next? it = some (c, s) ∧ test c = none
                       ∧ e = Parser.Error.unexpected (Parser.Stream.getPosition s) (some c))
                 ∧ Stream.decrementsRemaining it s
                 ∧ Stream.respectsPosition it s
              else s = it
                   ∧ e = Parser.Error.unexpected (Stream.getPosition s) none
                   ∧ Stream.respectsPosition it s⌝⟩⦄ := by
  cases Remaining.lt_or_eq _ it
  · mvcgen [Parser.tokenMap]
    simp [wp, tokenCore, Stream.next?, bind, Parser.setStream, pure, PredTrans.apply, Parser.run]
    have ⟨rem, ⟨c, hn⟩⟩ := @Stream.Next?OnInput.cond σ τ _ _ _ _ it (by grind)
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
  · mvcgen [Parser.tokenMap]
    intros
    simp [wp, tokenCore, Stream.next?, bind, Parser.getStream, pure, PredTrans.apply, Parser.run]
    have := @Stream.Next?OnEndOfInput.cond σ τ _ _ _  it (by grind)
    simp_all

@[simp] theorem respectsPosition_tokenMap (σ τ α : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  (test : τ → Option α)
    : respectsPosition _ _ ((tokenMap test) : SimpleParser σ τ α) := by
  dsimp [respectsPosition]
  intro it s heq
  grind [SimpleParser.of_wp_eq (tokenMap test) (Spec.tokenMap _ _ it test) it (by grind)]

@[simp] theorem decrementsRemainingOnSuccess_tokenMap (σ τ α : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] (test : τ → Option α)
    : decrementsRemainingOnSuccess _ _ ((tokenMap test) : SimpleParser σ τ α) := by
  dsimp [decrementsRemainingOnSuccess]
  and_intros
  intro it rem _ h1
  grind [SimpleParser.of_wp_eq (tokenMap test) (Spec.tokenMap _ _ it test) it (by grind)]

@[spec] theorem Spec.anyToken (σ τ : Type) [Parser.Stream σ τ]  [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃fun s => ⌜s = it⌝⦄
      (Parser.anyToken : SimpleParser σ τ τ)
      ⦃post⟨fun c s => ⌜0 < Stream.Remaining.remaining it
                       ∧ Stream.next? it = some (c, s)
                       ∧ Stream.decrementsRemaining it s
                       ∧ Stream.respectsPosition it s⌝,
           fun _ s => ⌜s = it ∧ 0 = Stream.Remaining.remaining it⌝⟩⦄ := by
  simp only [Parser.anyToken]
  mintro _
  mspec Spec.tokenMap
  · simp_all
  · simp_all

@[grind .] theorem respectsPosition_anyToken (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ]
    : respectsPosition _ _ (anyToken : SimpleParser σ τ τ) := by
  simp [anyToken]

@[simp] theorem decrementsRemainingOnSuccessOnSuccess_anyToken (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
    : decrementsRemainingOnSuccess _ _ (anyToken : SimpleParser σ τ τ) := by
  simp [anyToken]

@[spec] theorem Spec.lookAhead [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ respectsPosition _ _ p⌝⦄
      Parser.lookAhead p
      ⦃post⟨fun a s => ⌜it = s ∧ ∃ s', p it = Result.ok s' a⌝,
           fun e s => ⌜it = s ∧ ∃ s', p it = Result.error s' e⌝⟩⦄ := by
  mvcgen [Parser.lookAhead]
  simp only [SimpleParser.WP.tryCatch]
  simp [wp, bind, PredTrans.apply, Parser.run, pure]
  expose_names
  simp [respectsPosition] at h
  split
  · split
    · expose_names
      split at heq
      · expose_names
        grind [setPosition_of_getPosition_eq s s_2 (Stream.getPosition s) (by grind) (by grind)]
      · grind
    · grind
  · rename_i heq
    split
    all_goals(split at heq <;>
      (expose_names
       have := setPosition_eq_ok s_2 r
       grind [setPosition_of_getPosition_eq it s' (Stream.getPosition it)
                  (by grind) (by grind)]))

@[simp] theorem consumesNoInput_lookAhead [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  (p : SimpleParser  σ τ α) (hr : respectsPosition σ τ p)
    : consumesNoInput _ _ (lookAhead p) := by
  simp [consumesNoInput]
  intro it
  have := SimpleParser.of_wp_eq (lookAhead p) (Spec.lookAhead p it) it (by simp_all)
  grind

@[spec] theorem Spec.peek [Parser.Stream σ τ]  [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃fun s => ⌜s = it⌝⦄
      (Parser.peek : SimpleParser σ τ τ)
      ⦃post⟨fun c s => ⌜s = it ∧ (∃ s', Stream.next? it = some (c, s')) ∧ 0 < Stream.Remaining.remaining it⌝,
           fun _ s => ⌜s = it ∧ 0 = Stream.Remaining.remaining it⌝⟩⦄ := by
  cases Remaining.lt_or_eq _ it
  · mvcgen [Parser.peek] with grind [SimpleParser.of_wp_eq (Parser.anyToken) (Spec.anyToken _ _ it) it
                    (by simp_all)]
  · mvcgen [Parser.peek] with grind [SimpleParser.of_wp_eq (Parser.anyToken) (Spec.anyToken _ _ it) it
                    (by simp_all)]

@[spec] theorem Spec.withBacktracking [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Parser.respectsPosition _ _ p⌝⦄
      Parser.withBacktracking p
      ⦃post⟨fun a s => ⌜p it = .ok s a ∧ Stream.respectsPosition it s⌝,
           fun e s => ⌜s = it ∧ ∃ s', p it = .error s' e⌝⟩⦄ := by
  mvcgen [Parser.withBacktracking]
  simp only [SimpleParser.WP.tryCatch]
  simp [wp, bind, PredTrans.apply, Parser.run, pure]
  expose_names
  simp [respectsPosition] at h
  split
  · grind
  · rename_i s' _ _
    have := setPosition_of_getPosition_eq s s' r (by grind) (by grind)
    simp_all
    grind [setPosition_of_getPosition_eq it s' r (by grind) (by grind)]

@[simp] theorem decrementsRemainingOnSuccess_withBacktracking [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α)
  (h : respectsPosition _ _ p ∧ decrementsRemainingOnSuccess _ _ p)
    : decrementsRemainingOnSuccess _ _ (Parser.withBacktracking p) := by
  simp [decrementsRemainingOnSuccess]
  intro it
  have := SimpleParser.of_wp_eq (Parser.withBacktracking p) (Spec.withBacktracking p it) it (by
            simp_all)
  simp [respectsPosition, decrementsRemainingOnSuccess] at h
  grind

@[spec] theorem Spec.notFollowedBy [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] (p : SimpleParser  σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Parser.respectsPosition _ _ p⌝⦄
      Parser.notFollowedBy p
      ⦃post⟨fun _ s  => ⌜s = it ∧ ∃ e s', p it = .error s' e⌝,
           fun _ s  => ⌜s = it ∧ ∃ a s', p it = .ok s' a⌝⟩⦄ := by
  mvcgen [Parser.notFollowedBy]
  simp only [SimpleParser.WP.tryCatch]
  simp only [wp, bind, PredTrans.apply, Parser.run, pure]
  grind [SimpleParser.of_wp_eq (Parser.lookAhead p) (Spec.lookAhead p it) it (by simp_all)]

@[simp] theorem consumesNoInput_notFollowedBy [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  (p : SimpleParser  σ τ α) (hr : respectsPosition σ τ p)
    : consumesNoInput _ _ (Parser.notFollowedBy p) := by
  simp [consumesNoInput]
  intro it
  have := SimpleParser.of_wp_eq (Parser.notFollowedBy p) (Spec.notFollowedBy p it) it (by simp_all)
  grind

@[spec] theorem Spec.endOfInput [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃fun s => ⌜s = it⌝⦄
      (Parser.endOfInput : SimpleParser  σ τ Unit)
      ⦃post⟨fun _ s => ⌜s = it ∧ 0 = Stream.Remaining.remaining s⌝,
           fun _ s => ⌜s = it ∧ 0 < Stream.Remaining.remaining it⌝⟩⦄ := by
  mvcgen [Parser.endOfInput]
  all_goals grind [SimpleParser.of_wp_eq (Parser.anyToken) (Spec.anyToken _ _ it) it (by grind)]

theorem endOfInputConsumesNoInput [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
    : consumesNoInput _ _ (Parser.endOfInput : SimpleParser  σ τ Unit) := by
  simp [consumesNoInput]
  intro it
  have := SimpleParser.of_wp_eq Parser.endOfInput (Spec.endOfInput it) it (by
    simp_all)
  grind

@[spec] theorem Spec.eoption [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ respectsPosition _ _ p⌝⦄
      Parser.eoption p
      ⦃⇓ a s => ⌜match p it with
                       | .ok rem x => s = rem ∧ a = Sum.inl x
                                    ∧ Stream.respectsPosition it rem
                       | .error _ e => s = it ∧ a = Sum.inr e
                                    ∧ Stream.respectsPosition it s⌝⦄ := by
  mvcgen [Parser.eoption]
  simp [wp, bind, pure, respectsPosition, PredTrans.apply, Parser.run]
  intros
  split
  · split
    · grind
    · expose_names
      split at heq
      · simp_all
      · expose_names
        have := Stream.RespectsPosition.setPosition_of_getPosition_eq it a_2 (Stream.getPosition it)
                      (by grind) (by grind)
        and_intros <;> grind
  · grind

@[spec] theorem Spec.optional [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α) (it : σ)
    : ⦃fun s => ⌜s = it ∧ respectsPosition _ _ p⌝⦄
      Parser.optional p
      ⦃⇓ () s => ⌜match p it with
                     | .ok rem a => s = rem ∧ p it = Result.ok rem a
                                    ∧ Stream.respectsPosition it rem
                     | .error _ _ => s = it ∧ Stream.respectsPosition it s⌝⦄ := by
  mvcgen [Parser.optional]
  intros
  simp only [SimpleParser.WP.seqRight]
  mspec Spec.eoption
  simp_all
  grind

@[spec] theorem Spec.withErrorMessage [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α) (msg : String) (it : σ)
    : ⦃fun s => ⌜s = it ∧ Parser.respectsPosition _ _ p⌝⦄
      Parser.withErrorMessage msg p
      ⦃post⟨fun a s => ⌜(∃ rem, p it = .ok rem a ∧ s = rem)
                        ∧ Stream.respectsPosition it s⌝,
           fun e s => ⌜(∃ e', p it = .error s e'
                            ∧ (Error.addMessage e' (Stream.getPosition s) msg) = e)
                        ∧ Stream.respectsPosition it s⌝⟩⦄ := by
  mvcgen [Parser.withErrorMessage]
  simp only [SimpleParser.WP.tryCatch, SimpleParser.WP.throwErrorWithMessage]
  simp only [wp, PredTrans.apply, Parser.run]
  rename_i h
  simp [respectsPosition] at h
  grind

@[simp] theorem respectsPosition_withErrorMessage (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α)
  (h : respectsPosition _ _ p) (msg : String)
      : respectsPosition _ _ (withErrorMessage msg p) := by
  simp [respectsPosition]

  intro it
  grind [SimpleParser.of_wp_eq (Parser.withErrorMessage msg p) (Spec.withErrorMessage p msg it) it (by grind)]

@[simp] theorem decrementsRemainingOnSuccess_withErrorMessage (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.RespectsPosition σ τ] (p : SimpleParser σ τ α) (msg : String)
  (h : respectsPosition _ _ p ∧ decrementsRemainingOnSuccess _ _ p)
      : decrementsRemainingOnSuccess _ _ (withErrorMessage msg p) := by
  simp [decrementsRemainingOnSuccess]
  simp [decrementsRemainingOnSuccess] at h
  intro it
  grind [SimpleParser.of_wp_eq (Parser.withErrorMessage msg p) (Spec.withErrorMessage p msg it) it (by grind)]

@[spec] theorem Spec.token [Parser.Stream σ τ]  [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] [BEq τ]
  [LawfulBEq τ] (it : σ) (tk : τ)
    : ⦃fun s => ⌜s = it⌝⦄
      (Parser.token tk : SimpleParser σ τ τ)
      ⦃post⟨fun c s => ⌜c = tk ∧ 0 < Stream.Remaining.remaining it
                        ∧ Stream.decrementsRemaining it s
                        ∧ Stream.respectsPosition it s⌝,
           fun _ s => ⌜Stream.respectsPosition it s⌝⟩⦄ := by
  mvcgen [Parser.token]
  simp [tokenFilter]
  mvcgen with grind

@[simp] theorem respectsPosition_token (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  [BEq τ] [LawfulBEq τ] (tk : τ)
    : respectsPosition _ _ ((token tk) : SimpleParser σ τ τ) := by
  simp [respectsPosition]

  intro it
  grind [SimpleParser.of_wp_eq (Parser.token tk) (Spec.token it tk) it (by grind)]

@[simp] theorem decrementsRemainingOnSuccess_token (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  [BEq τ] [LawfulBEq τ] (tk : τ)
    : decrementsRemainingOnSuccess _ _ (Parser.token tk : SimpleParser σ τ τ) := by
  dsimp [decrementsRemainingOnSuccess]
  intro it _ _ _
  grind [SimpleParser.of_wp_eq (Parser.token tk) (Spec.token it tk) it (by grind)]

@[spec] theorem Spec.char [Parser.Stream σ Char]  [Stream.Remaining σ]
  [Stream.RespectsPosition σ Char] [Stream.Next?OnInput σ Char] [Stream.Next?OnEndOfInput σ Char]
  (it : σ) (tk : Char)
    : ⦃fun s => ⌜s = it⌝⦄
      (Char.char tk : SimpleParser σ Char Char)
      ⦃post⟨fun c s => ⌜c = tk ∧ 0 < Stream.Remaining.remaining it
                        ∧ Stream.decrementsRemaining it s
                        ∧ Stream.respectsPosition it s⌝,
           fun _ s => ⌜Stream.respectsPosition it s⌝⟩⦄ := by
  mvcgen [Char.char]
  · simp_all
  · grind [SimpleParser.of_wp_eq (Parser.token tk) (Spec.token it tk) it (by simp_all)]
  · grind [SimpleParser.of_wp_eq (Parser.token tk) (Spec.token it tk) it (by simp_all)]

@[simp] theorem respectsPosition_char (σ : Type) [Parser.Stream σ Char] [Stream.Remaining σ]
  [Stream.RespectsPosition σ Char] [Stream.Next?OnInput σ Char]
  [Stream.Next?OnEndOfInput σ Char] (tk : Char)
    : respectsPosition _ _ ((Char.char tk) : SimpleParser σ Char Char) := by
  simp [Char.char]

@[simp] theorem decrementsRemainingOnSuccess_char (σ : Type) [Parser.Stream σ Char] [Stream.Remaining σ]
  [Stream.RespectsPosition σ Char] [Stream.Next?OnInput σ Char]
  [Stream.Next?OnEndOfInput σ Char] (tk : Char)
    : decrementsRemainingOnSuccess _ _ ((Char.char tk) : SimpleParser σ Char Char) := by
  simp [Char.char]
