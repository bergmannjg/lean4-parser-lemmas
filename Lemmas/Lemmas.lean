import Init.Meta
import Parser
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

import Lemmas.Basic

open Lean Lean.Syntax Parser Parser.Char

open Std.Do

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

@[spec] theorem getPositionSpec [Parser.Stream σ τ] (it : σ)
    : ⦃⌜True⌝⦄
      (getPosition : SimpleParser σ τ (Stream.Position σ)) it
      ⦃post⟨fun r => ⌜∃ pos, r = Result.ok it pos
                        ∧ pos = Parser.Stream.getPosition it⌝⟩⦄ := by
  mintro _
  unfold wp Id.instWP Id.run getPosition Stream.getPosition
    getStream pure Id.instMonad Applicative.toPure Monad.toApplicative
    Functor.map instMonadParserT Applicative.toFunctor
    bind pure Applicative.toPure
  grind

theorem getPositionResultEqOk [Parser.Stream σ τ] (it : σ)
    : ∃ pos, (getPosition : SimpleParser σ τ (Stream.Position σ)) it = Result.ok it pos := by
  have hg := getPositionSpec it (by simp)
  simp [wp, Id.run] at hg
  grind

@[spec] theorem setPositionSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (it : σ) (pos : Stream.Position σ)
  : ⦃⌜Stream.SetPositionPrecondition.cond it pos⌝⦄
    (setPosition pos : SimpleParser σ τ Unit) it
    ⦃post⟨fun r => ⌜∃ rem, r = Result.ok rem () ∧ pos = Parser.Stream.getPosition rem
                           ∧ Stream.RespectsPosition.respectsPosition τ it rem⌝⟩⦄ := by
  mintro _
  intro h
  simp at h
  simp [wp, Id.run, setPosition, bind, getStream, setStream, pure]
  have ⟨r, And.intro hs ⟨rem, hr⟩⟩ := Stream.SetPositionPrecondition.validResult it pos h
  grind

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

@[spec] theorem tokenMapSpec (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  (it : σ) (test : τ → Option α)
    : ⦃⌜0 < Stream.Remaining.remaining it⌝⦄
      ((tokenMap test) : SimpleParser σ τ α) it
      ⦃post⟨fun r => ⌜
        ∃ (rem : σ), (∃ c,
            (match test c with
            | some a => r = Parser.Result.ok rem a
                        ∧ Stream.decrementsRemaining it rem
                        ∧ Stream.RespectsPosition.respectsPosition τ it rem
            | none => (∃ (p : Stream.Position σ), p = Parser.Stream.getPosition rem
                        ∧ r = Parser.Result.error rem (Parser.Error.unexpected p (some c)))
                        ∧ Stream.decrementsRemaining it rem
                        ∧ Stream.RespectsPosition.respectsPosition τ it rem))⌝⟩⦄ := by
  mintro _
  simp [wp, tokenMap, tokenCore, Stream.next?, bind, getStream, setStream, pure, Id.run]
  intro h
  have ⟨rem, ⟨c, hn⟩⟩ := @Stream.Next?OnInput.cond σ τ _ _ _ _ _ it h
  simp_all
  exact ⟨rem, by exact ⟨c, by
      split
      · grind
      · rename_i heq
        rw [heq]
        simp
        and_intros
        · have := Parser.getPositionSpec rem (by simp)
          simp [wp, Id.run] at this
          simp [throwUnexpected, bind, throw, throwThe, MonadExceptOf.throw, pure]
          simp_all
        · grind
        · grind⟩⟩

@[spec] theorem tokenMapEndOfInputSpec (σ τ : Type) [Parser.Stream σ τ]  [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ][Stream.Next?OnEndOfInput σ τ]
  (it : σ) (test : τ → Option α)
    : ⦃⌜ Stream.ValidPosition.valid it ∧ 0 = Stream.Remaining.remaining it⌝⦄
      ((tokenMap test) : SimpleParser σ τ α) it
      ⦃post⟨fun r => ⌜∃ e, r = .error it e⌝⟩⦄ := by
  mintro _
  dsimp [wp, tokenMap, tokenCore, Stream.next?, bind, getStream, pure,
    PredTrans.pure, PredTrans.apply, throwUnexpected, Id.run, throw, throwThe,
    MonadExceptOf.throw]
  intro h
  have := @Stream.Next?OnEndOfInput.cond σ τ _ _ _ (by assumption) it h.left h.right
  rw [this]
  simp_all
  have hg := getPositionSpec it (by simp)
  simp [wp, Id.run] at hg
  rw [hg]
  simp_all

@[simp] theorem tokenMapRespectsPosition (σ τ α : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ] (test : τ → Option α)
    : respectsPosition _ _ ((tokenMap test) : SimpleParser σ τ α) := by
  dsimp [respectsPosition]
  intro it rem h
  cases remainingLtOrEq _ it
  · have := tokenMapSpec _ _ it test (by simp_all)
    simp [wp, Id.run] at this
    grind
  · have := tokenMapEndOfInputSpec _ _ it test (by grind)
    simp [wp, Id.run] at this
    have ⟨e, he⟩ := this
    simp_all
    intro _
    exact Stream.RespectsPosition.isEquivalence.refl rem

@[simp] theorem tokenMapDecrementsRemainingOnSuccessOnSuccess (σ τ α : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] (test : τ → Option α)
    : decrementsRemainingOnSuccess _ _ ((tokenMap test) : SimpleParser σ τ α) := by
  dsimp [decrementsRemainingOnSuccess]
  and_intros
  intro it rem _ h1
  cases remainingLtOrEq _ it
  · have := tokenMapSpec _ _ it test (by simp_all)
    simp [wp, Id.run] at this
    grind
  · have := tokenMapEndOfInputSpec _ _ it test (by grind)
    have ⟨e, he⟩ := this
    dsimp [Id.run] at he
    simp_all

@[spec] theorem anyTokenSpec (σ τ : Type) [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] (it : σ)
    : ⦃⌜0 < Stream.Remaining.remaining it⌝⦄
      (anyToken : SimpleParser σ τ τ) it
      ⦃post⟨fun r => ⌜∃ rem, (∃ c, r = Parser.Result.ok rem c ∧ Stream.decrementsRemaining it rem
                                    ∧ Stream.RespectsPosition.respectsPosition τ it rem)⌝⟩⦄ := by
  mvcgen [anyToken]

@[spec] theorem anyTokenEndOfInputSpec (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ 0 = Stream.Remaining.remaining it⌝⦄
      (anyToken : SimpleParser σ τ τ) it
      ⦃post⟨fun r => ⌜∃ e, r = .error it e⌝⟩⦄ := by
  mintro _
  simp [wp]
  intro h1 h2
  simp [anyToken, Id.run]
  exact tokenMapEndOfInputSpec _ _ it some (by grind)

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
    : ⦃⌜Stream.ValidPosition.valid it ∧ respectsPosition _ _ p⌝⦄
      lookAhead p it
      ⦃post⟨fun r => ⌜match r with
                     | .ok rem a => it = rem ∧ ∃ rem', p it = Result.ok rem' a
                     | .error rem e => it = rem ∧ ∃ rem', p it = Result.error rem' e⌝⟩⦄ := by
  mintro _
  simp [wp, lookAhead, bind, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind, ParserT.run,
          Id.run, pure]
  intro hv hp
  simp [respectsPosition] at hp
  have hp := hp it hv
  split
  · rename_i heq
    split at heq
    · rename_i s a heq_1
      have := getPositionSpec it (by simp)
      simp [wp, Id.run] at this
      split at heq
      · rename_i heq_2
        split at heq_2
        · simp_all
          rename_i heq_3
          split at heq_3
          · rename_i s_3 _ _
            have := Result.ok.inj heq_3
            split at heq
            · split at heq_3 <;> simp_all
            · split at heq_3
              · expose_names
                have := setPositionOfGetPositionEq it s_3 a
                grind only
              · grind only
          · simp_all
        · split at heq_2 <;> simp_all
      · grind
    · grind
  · rename_i heq
    split at heq
    · rename_i a heq_1
      have := getPositionSpec it (by simp)
      simp [wp, Id.run] at this
      split at heq
      · rename_i heq_2
        split at heq_2 <;> grind
      · rename_i heq_2
        split at heq_2
        · grind
        · rename_i s_2 _ heq_3
          expose_names
          split at heq_3
          · rename_i s_3 _ _
            split at heq_3
            · grind
            · expose_names
              have := setPositionOfGetPositionFalseIfRespectsPosition s_3 s_4 a
                            (by assumption) (by simp_all)
              grind only
          · split at heq_2
            · expose_names
              split at heq_2
              · simp_all
              · expose_names
                simp [throw, throwThe, MonadExceptOf.throw, pure] at heq_6
                and_intros
                · have := setPositionOfGetPositionEq s s_2 a (by grind) (by grind) (by grind)
                  grind
                · grind
            · expose_names
              have := setPositionOfGetPositionFalseIfRespectsPosition s_3 s_4 a
                            (by assumption) (by simp_all; grind)
              grind only
    · grind [getPositionResultEqOk it]

@[simp] theorem lookAheadConsumesNoInput [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] [Stream.AllValid σ]
  (p : SimpleParser  σ τ α) (hr : respectsPosition σ τ p)
    : consumesNoInput _ _ (lookAhead p) := by
  simp [consumesNoInput]
  intro it
  have := lookAheadSpec p it (by and_intros; exact Stream.AllValid.valid it; grind)
  simp [wp, Id.run] at this
  grind

@[spec] theorem peekSpec [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  [Stream.SetPositionPrecondition σ τ] (it : σ)
    : ⦃⌜0 < Stream.Remaining.remaining it⌝⦄
      (peek : SimpleParser σ τ τ) it
      ⦃post⟨fun r => ⌜∃ c, r = Parser.Result.ok it c⌝⟩⦄ := by
  mintro _
  intro h
  mvcgen [peek]
  · simp [respectsPosition]
    and_intros
    · exact Stream.ValidPosition.validOfRemaining it h
    · intro it
      have := anyTokenRespectsPosition σ τ it
      grind
  · have ht := anyTokenSpec _ _ it h
    simp [wp, Id.run] at ht
    grind

@[spec] theorem peekEndOfInputSpec [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
  [Stream.SetPositionPrecondition σ τ] (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ 0 = Stream.Remaining.remaining it⌝⦄
      (peek : (SimpleParser  σ τ) τ) it
      ⦃post⟨fun r => ⌜∃ e, r = Parser.Result.error it e⌝⟩⦄ := by
  mintro _
  intro h
  have ht := anyTokenEndOfInputSpec _ _ it (by grind)
  simp [wp, Id.run] at ht
  simp [wp, Id.run]
  have := lookAheadSpec anyToken it (by
    and_intros
    · simp_all
    · exact anyTokenRespectsPosition σ τ)
  simp [wp, Id.run] at this
  grind

@[spec] theorem withBacktrackingSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ Parser.respectsPosition _ _ p⌝⦄
      withBacktracking p it
      ⦃post⟨fun r => ⌜match r with
                     | .ok rem a => p it = .ok rem a
                        ∧ Stream.RespectsPosition.respectsPosition τ it rem
                     | .error it e => ∃ rem, p it = .error rem e⌝⟩⦄ := by
  mintro _
  simp [wp,withBacktracking, Id.run, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind,
        ParserT.run, pure, throw, respectsPosition]
  intro _ _
  split
  · expose_names
    split at heq
    · expose_names
      split at heq
      · have := getPositionSpec it (by simp)
        simp [wp, Id.run] at this
        grind
      · split at heq <;> simp_all
    · grind
  · expose_names
    split at heq
    · split at heq
      · grind
      · expose_names
        have := getPositionSpec it (by simp)
        simp [wp, Id.run] at this
        split at heq
        · expose_names
          have := Result.error.inj heq
          have := setPositionOfGetPositionEq it s_1
                  (by assumption) (by assumption) (by grind)
          exact ⟨s_1, by grind⟩
        · expose_names
          have := Parser.setPositionOfGetPositionFalseIfRespectsPosition s_1 s_2 a
                            (by assumption) (by grind)
          grind
    · have := getPositionResultEqOk it
      grind

@[simp] theorem withBacktrackingOfDecrementsRemaining [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.AllValid σ] (p : SimpleParser σ τ α) (h : respectsPosition _ _ p
        ∧ decrementsRemainingOnSuccess _ _ p)
    : decrementsRemainingOnSuccess _ _ (withBacktracking p) := by
  simp [decrementsRemainingOnSuccess]
  intro it
  have := withBacktrackingSpec p it (by and_intros; exact Stream.AllValid.valid it; grind)
  simp [wp, Id.run] at this
  simp [respectsPosition, decrementsRemainingOnSuccess] at h
  grind

@[spec] theorem notFollowedBySpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser  σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ Parser.respectsPosition _ _ p⌝⦄
      notFollowedBy p it
      ⦃post⟨fun r => ⌜match p it with
                     | .ok _ _ => ∃ e, r = .error it e
                     | .error _ _ => r = .ok it ()⌝⟩⦄ := by
  mintro _
  simp [wp, notFollowedBy, Id.run, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind,
    ParserT.run, pure, throwUnexpected, throw, throwThe, MonadExceptOf.throw]
  intro h1 h2
  have ha := lookAheadSpec p it (by and_intros <;> simp_all)
  simp [wp, Id.run] at ha
  split
  · split
    · expose_names
      split at heq_1
      · expose_names
        split at heq_2
        · expose_names
          simp_all
          split
          · expose_names
            split
            · expose_names
              have := Result.ok.inj heq_2
              have := getPositionSpec it (by simp)
              simp [wp, Id.run] at this
              simp_all
            · have := getPositionResultEqOk s
              simp_all
          · grind
        · split
          · split <;> simp_all
          · simp_all
      · split
        · split
          · expose_names
            have := Result.ok.inj heq_1
            have := getPositionSpec it (by simp)
            simp [wp, Id.run] at this
            simp_all
          · have := getPositionResultEqOk s
            simp_all
        · grind
    · grind
  · grind

@[simp] theorem notFollowedByConsumesNoInput [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ] [Stream.AllValid σ]
  (p : SimpleParser  σ τ α) (hr : respectsPosition σ τ p)
    : consumesNoInput _ _ (notFollowedBy p) := by
  simp [consumesNoInput]
  intro it
  have := notFollowedBySpec p it (by and_intros; exact Stream.AllValid.valid it; grind)
  simp [wp, Id.run] at this
  grind

@[spec] theorem endOfInputSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it⌝⦄
      (endOfInput : SimpleParser  σ τ Unit) it
      ⦃post⟨fun r => ⌜if 0 < Stream.Remaining.remaining it
                      then ∃ e, r = .error it e
                      else r = .ok it ()⌝⟩⦄ := by
  mintro _
  intro h
  split
  · have ht := anyTokenSpec _ _ it (by grind only [= SPred.down_pure])
    simp [wp, Id.run] at ht
    mvcgen [endOfInput]
    . and_intros
      · grind
      · intro it
        have := anyTokenRespectsPosition σ τ it
        grind
    . split <;> grind
  · have ht := anyTokenEndOfInputSpec _ _ it (by grind only [= SPred.down_pure])
    simp [wp, Id.run] at ht
    mvcgen [endOfInput]
    · and_intros
      · simp_all
      · exact anyTokenRespectsPosition σ τ
    · expose_names
      split <;> simp_all

theorem endOfInputConsumesNoInput [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ] [Stream.AllValid σ]
    : consumesNoInput _ _ (endOfInput : SimpleParser  σ τ Unit) := by
  simp [consumesNoInput]
  intro it
  have := endOfInputSpec it (by and_intros; exact Stream.AllValid.valid it)
  simp [wp, Id.run] at this
  grind

@[spec] theorem eoptionSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ respectsPosition _ _ p⌝⦄
      eoption p it
      ⦃post⟨fun r => ⌜match p it with
                     | .ok rem x => r = .ok rem (Sum.inl x)
                                          ∧ Stream.RespectsPosition.respectsPosition τ it rem
                     | .error _ e => r = .ok it (Sum.inr e)⌝⟩⦄ := by
  mintro _
  simp [wp, eoption, bind, pure, Id.run, respectsPosition]
  intro hv hp
  split
  · split <;> grind
  · split
    · grind
    · rename_i rem _ _
      simp_all
      and_intros
      · generalize hg : Stream.getPosition it = p
        exact Parser.Stream.RespectsPosition.setPositionOfGetPositionEq it rem p hv hg (by grind)
      · grind

@[spec] theorem optionalSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ respectsPosition _ _ p⌝⦄
      optional p it
      ⦃post⟨fun r => ⌜match p it with
                     | .ok rem _ => r = .ok rem ()
                                      ∧ Stream.RespectsPosition.respectsPosition τ it rem
                     | .error _ _ => r = .ok it ()⌝⟩⦄ := by
  mvcgen [optional]
  simp [wp, Id.run, SeqRight.seqRight, bind, pure]
  intro hv hr
  have he := eoptionSpec p it (by simp_all)
  simp [wp, Id.run] at he
  split
  · split
    · split at he
      · grind
      · simp_all
    · simp_all
  · split
    · split at he
      · simp_all
      · grind
    · simp_all

@[spec] theorem withErrorMessageSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (msg : String) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ Parser.respectsPosition _ _ p⌝⦄
      withErrorMessage msg p it
      ⦃post⟨fun r => ⌜match p it with
                     | .ok rem a => r = .ok rem a
                            ∧ Stream.RespectsPosition.respectsPosition τ it rem
                     | .error _ _ => match r with | .ok _ _ => false | .error rem _ => true
                            ∧ Stream.RespectsPosition.respectsPosition τ it rem⌝⟩⦄ := by
  mintro _
  simp [wp, withErrorMessage, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, pure, Id.run,
        bind, throwErrorWithMessage, throw, throwThe, MonadExceptOf.throw, ParserT.run]
  intro hv hr
  simp [respectsPosition] at hr
  have hr := hr it (by grind)
  split
  · split <;> simp_all
  · split
    · expose_names
      split at heq_1
      · simp_all
      · split at heq_1
        · simp_all
        · expose_names
          have := getPositionResultEqOk s
          simp_all
    · expose_names
      split at heq_1
      · simp_all
      · split at heq_1
        · expose_names
          have := Parser.getPositionSpec s (by simp)
          simp [wp, Id.run] at this
          rw [this] at heq_3
          have := getPositionResultEqOk s
          simp_all
          have := Result.error.inj heq
          have := Result.error.inj heq_1
          have := Result.ok.inj heq_3
          simp_all
        · expose_names
          have := getPositionResultEqOk s
          simp_all

@[simp] theorem withErrorMessageRespectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  [Stream.AllValid σ] (p : SimpleParser σ τ α) (h : respectsPosition _ _ p) (msg : String)
      : respectsPosition _ _ (withErrorMessage msg p) := by
  simp [respectsPosition]
  have h : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro it h
  have hw := withErrorMessageSpec p msg it (by grind)
  simp [wp, Id.run] at hw
  split at hw
  · simp_all
  · split <;> simp_all

@[simp] theorem withErrorMessageDecrementsRemainingOnSuccess (σ τ : Type) [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.SetPositionPrecondition σ τ]
  [Stream.AllValid σ] (p : SimpleParser σ τ α) (msg : String)
  (h : respectsPosition _ _ p ∧ decrementsRemainingOnSuccess _ _ p)
      : decrementsRemainingOnSuccess _ _ (withErrorMessage msg p) := by
  simp [decrementsRemainingOnSuccess]
  have : ∀ (it : σ), Stream.ValidPosition.valid it := Stream.AllValid.valid
  intro it
  have := withErrorMessageSpec p msg it (by grind)
  simp [wp, Id.run] at this
  simp [respectsPosition, decrementsRemainingOnSuccess] at h
  simp_all
  grind
