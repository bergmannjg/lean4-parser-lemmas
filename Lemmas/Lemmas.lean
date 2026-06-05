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
  simp [wp, Id.run]
  have ⟨r, And.intro hs ⟨rem, hr⟩⟩ := Stream.SetPositionPrecondition.validResult it pos h
  exact ⟨rem, by grind⟩

/-- setPosition after applying a respectful parser cannot give an error -/
theorem setPositionOfGetPositionFalseIfRespectsPosition  [Parser.Stream σ τ]
  [Stream.Remaining σ] [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  [Stream.SetPositionPrecondition σ τ]
  (s1 s2 s3 s4 : σ) (p : Stream.Position σ) (e : Error.Simple σ τ)
  (h0 : Stream.ValidPosition.valid s1)
  (h1 : (Parser.getPosition : SimpleParser σ τ (Stream.Position σ)) s1 = Result.ok s2 p)
  (h2 : Stream.RespectsPosition.respectsPosition τ s2 s3)
  (h3 : (setPosition p : SimpleParser σ τ Unit) s3 = Result.error s4 e)
    : False := by
  have hg := getPositionSpec s1 (by simp)
  simp [wp, Id.run] at hg
  have ⟨r, And.intro hs ⟨rem, hr⟩⟩ := Stream.SetPositionPrecondition.validResult s3 p (by
    exact Stream.SetPositionPrecondition.ofGetPosition s1 s2 s3 p (by assumption) h1 h2)
  simp_all

@[spec] theorem tokenMapSpec (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
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
  simp [wp, tokenMap, tokenCore, Stream.next?, bind, getStream, setStream]
  intro h
  have ⟨rem, ⟨c, hn⟩⟩ := @Stream.Next?OnInput.cond σ τ _ _ _ _ _ it h
  simp_all
  exact ⟨rem, by exact ⟨c, by
      split
      · rename_i heq
        rw [heq]
        simp_all
        rfl
      · rename_i heq
        rw [heq]
        simp
        and_intros
        · have := Parser.getPositionSpec rem (by simp)
          simp [wp, Id.run] at this
          simp [throwUnexpected, bind, Id.run, throw, throwThe, MonadExceptOf.throw, pure]
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
    PredTrans.pure, PredTrans.apply, throwUnexpected, Id.run]
  intro h
  have := @Stream.Next?OnEndOfInput.cond σ τ _ _ _ (by assumption) it h.left h.right
  rw [this]
  simp_all
  have hg := getPositionSpec it (by simp)
  simp [wp, Id.run] at hg
  rw [hg]
  simp_all

@[spec] theorem anyTokenSpec (σ τ : Type) [Parser.Stream σ τ]  [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] (it : σ)
    : ⦃⌜0 < Stream.Remaining.remaining it⌝⦄
      (anyToken : SimpleParser σ τ τ) it
      ⦃post⟨fun r => ⌜∃ rem, (∃ c, (r = Parser.Result.ok rem c ∧ Stream.decrementsRemaining it rem
                                    ∧ Stream.RespectsPosition.respectsPosition τ it rem))⌝⟩⦄ := by
  mvcgen [anyToken]

@[spec] theorem anyTokenEndOfInputSpec (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnEndOfInput σ τ] (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ 0 = Stream.Remaining.remaining it⌝⦄
      (anyToken : SimpleParser σ τ τ) it
      ⦃post⟨fun r => ⌜∃ e, r = .error it e⌝⟩⦄ := by
  mintro _
  simp [wp]
  intro h1 h2
  simp [anyToken, Id.run]
  exact tokenMapEndOfInputSpec _ _ it some (by grind)

@[grind .] theorem remainingLtOrEq (σ : Type) [Stream.Remaining σ] (it : σ)
    : 0 < Stream.Remaining.remaining it ∨ 0 = Stream.Remaining.remaining it := by
  grind

theorem anyTokenrespectsPosition (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ]
  [Stream.Next?OnEndOfInput σ τ]
    : respectsPosition _ _ (anyToken : SimpleParser σ τ τ):= by
  dsimp [respectsPosition]
  intro it rem h
  cases remainingLtOrEq _ it
  · have := anyTokenSpec _ _ it (by simp_all)
    simp [wp, Id.run] at this
    grind
  · have := anyTokenEndOfInputSpec _ _ it (by grind)
    simp [wp, Id.run] at this
    have ⟨e, he⟩ := this
    simp_all
    intro _
    exact Stream.RespectsPosition.respectsPositionEq rem

theorem anyTokenDecrementsRemainingOnSuccessOnSuccess (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.Next?OnInput σ τ] [Stream.Next?OnEndOfInput σ τ]
    : decrementsRemainingOnSuccess _ _ (anyToken : SimpleParser σ τ τ) := by
  dsimp [decrementsRemainingOnSuccess]
  and_intros
  · intro it rem _ h1 h2
    cases remainingLtOrEq _ it
    · have := anyTokenSpec _ _ it (by simp_all)
      simp [wp, Id.run] at this
      grind
    · have := anyTokenEndOfInputSpec _ _ it (by grind)
      have ⟨e, he⟩ := this
      dsimp [Id.run] at he
      simp_all
  · intro it rem h1 h2
    cases remainingLtOrEq _ it
    · have := anyTokenSpec _ _ it (by simp_all)
      simp [wp, Id.run] at this
      grind
    · have := anyTokenEndOfInputSpec _ _ it (by grind)
      have ⟨e, he⟩ := this
      dsimp [Id.run] at he
      simp_all
      exact Stream.RespectsPosition.respectsPositionEq rem

@[spec] theorem lookAheadSpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ 0 < Stream.Remaining.remaining it ∧ respectsPosition _ _ p⌝⦄
      lookAhead p it
      ⦃post⟨fun r => ⌜match r with
                     | .ok rem a => it = rem ∧ ∃ rem', p it = Result.ok rem' a
                     | .error rem e => it = rem ∧ ∃ rem', p it = Result.error rem' e⌝⟩⦄ := by
  mintro _
  simp [wp, lookAhead, bind, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind, ParserT.run, Id.run, pure]
  intro h _ _
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
                have := @Stream.RespectsPosition.setPositionOfGetPositionEq _ _ _ _ _ _ a it s s_3 s_4
                            (by grind) (by simp_all) (by grind)
                grind only
              · grind only
          · simp_all
        · grind
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
              have := setPositionOfGetPositionFalseIfRespectsPosition it s s_3 s_4 a e_3
                            (by assumption) heq_1 (by simp_all; grind) (by grind)
              grind only
          · split at heq_2
            · expose_names
              have := @Stream.RespectsPosition.setPositionOfGetPositionEq _ _ _ _  _ _ a it s s_3 s_1
                            (by assumption) heq_1 (by simp_all; grind) (by grind)
              grind only
            · expose_names
              have := setPositionOfGetPositionFalseIfRespectsPosition it s s_3 s_4 a e_4
                            (by assumption) heq_1 (by simp_all; grind) (by grind)
              grind only
    · grind [getPositionResultEqOk it]

@[spec] theorem lookAheadEndOfInputSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ][Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ 0 = Stream.Remaining.remaining it ∧ respectsPosition _ _ p ∧ ∃ e, p it = .error it e⌝⦄
      lookAhead p it
      ⦃post⟨fun r => ⌜∃ e, r = .error it e⌝⟩⦄ := by
  mintro _
  simp [wp, lookAhead, bind, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind, ParserT.run, Id.run, pure]
  intro h _ _ _ _
  split
  · expose_names
    have := getPositionSpec it (by simp)
    simp [wp, Id.run] at this
    split
    · expose_names
      split at heq_1
      · expose_names
        split at heq_2
        · split at heq_2
          · split <;> grind
          · expose_names
            have := setPositionOfGetPositionFalseIfRespectsPosition it s s s_4 a e
                            (by assumption) heq (by grind) (by grind)
            grind
        · simp_all
      · split at heq_1
        · split <;> simp_all
        · expose_names
          have := setPositionOfGetPositionFalseIfRespectsPosition it s s s_3 a e
                            (by assumption) heq (by grind) (by grind)
          grind
    · have := getPositionSpec it (by simp)
      simp [wp, Id.run] at this
      expose_names
      split at heq_1
      · expose_names
        split at heq_2
        · split at heq_2 <;> simp_all
        · simp_all
      · expose_names
        split at heq_2
        · split at heq_2 <;> grind
        · expose_names
          simp_all
          split at heq_1
          · exact @Stream.RespectsPosition.setPositionOfGetPositionEq _ _ _ _ _ _ a it s s s_1
                      (by assumption) heq (by grind) (by grind)
                  |> Eq.symm
          · expose_names
            have : s_2 = s := by grind
            rw [this] at heq_4
            have := setPositionOfGetPositionFalseIfRespectsPosition s s s s_4 a e_3
                            (by grind) (by grind) (by grind)
            grind
  · have := getPositionResultEqOk it
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
  · simp
    and_intros
    · exact Stream.ValidPosition.validOfRemaining it h
    · grind
    · intro it
      have := anyTokenrespectsPosition σ τ it
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
  have := lookAheadEndOfInputSpec anyToken it (by
    and_intros
    · simp_all
    · grind
    · exact anyTokenrespectsPosition σ τ
    · grind)
  simp [wp, Id.run] at this
  grind

@[spec] theorem withBacktrackingRespectsPositionSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ Parser.respectsPosition _ _ p⌝⦄
      withBacktracking p it
      ⦃post⟨fun r => ⌜match r with
                     | .ok rem a => p it = .ok rem a
                        ∧ Stream.RespectsPosition.respectsPosition τ it rem
                     | .error rem _ => it = rem⌝⟩⦄ := by
  mintro _
  simp [wp,withBacktracking, Id.run, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind,
        ParserT.run, pure, throw]
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
          simp_all
          exact @Stream.RespectsPosition.setPositionOfGetPositionEq _ _ _ _ _ _ a it s s_1 rem
                  (by assumption) heq_1 (by grind) heq_3
        · expose_names
          have := Parser.setPositionOfGetPositionFalseIfRespectsPosition it s s_1 s_2 a e_2
                            (by assumption) heq_1 (by grind) (by grind)
          grind
    · have := getPositionResultEqOk it
      grind

@[spec] theorem withBacktrackingOfDecrementsRemainingSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ Parser.decrementsRemainingOnSuccess _ _ p⌝⦄
      withBacktracking p it
      ⦃post⟨fun r => ⌜match r with
                     | .ok rem a => p it = .ok rem a
                        ∧ Stream.RespectsPosition.respectsPosition τ it rem
                        ∧ Stream.decrementsRemaining it rem
                     | .error rem _ => it = rem⌝⟩⦄ := by
  mintro _
  simp [wp,withBacktracking, Id.run, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind,
        ParserT.run, pure, throw]
  intro _ _ _
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
          simp_all
          exact @Stream.RespectsPosition.setPositionOfGetPositionEq _ _ _ _ _ _ a it s s_1 rem
                  (by assumption) heq_1 (by grind) heq_3
        · expose_names
          have := Parser.setPositionOfGetPositionFalseIfRespectsPosition it s s_1 s_2 a e_2
                            (by assumption) heq_1 (by grind) (by grind)
          grind
    · have := getPositionResultEqOk it
      grind

@[spec] theorem notFollowedBySpec [Parser.Stream σ τ] [Stream.Remaining σ] [Stream.ValidPosition σ]
  [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser  σ τ α) (it : σ)
    : ⦃⌜0 < Stream.Remaining.remaining it ∧ Parser.respectsPosition _ _ p⌝⦄
      notFollowedBy p it
      ⦃post⟨fun r => ⌜match p it with
                     | .ok _ _ => ∃ e, r = .error it e
                     | .error _ _ => r = .ok it ()⌝⟩⦄ := by
  mintro _
  simp [wp, notFollowedBy, Id.run, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind,
    ParserT.run, pure, throwUnexpected, throw, throwThe, MonadExceptOf.throw]
  intro h1 h2
  have ha := lookAheadSpec p it (by
    and_intros
    · exact Stream.ValidPosition.validOfRemaining it h1
    · grind
    · simp_all)
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

@[spec] theorem notFollowedByEndOfInputSpec [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ] [Stream.SetPositionPrecondition σ τ]
  (p : SimpleParser  σ τ α) (it : σ)
    : ⦃⌜Stream.ValidPosition.valid it ∧ 0 = Stream.Remaining.remaining it ∧ Parser.respectsPosition _ _ p ∧ ∃ e, p it = .error it e⌝⦄
      notFollowedBy p it
      ⦃post⟨fun r => ⌜r = .ok it ()⌝⟩⦄ := by
  mintro _
  simp [wp, notFollowedBy, Id.run, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, bind,
    ParserT.run, pure, throwUnexpected, throw, throwThe, MonadExceptOf.throw]
  intro h _ _ _ _
  have ha := lookAheadEndOfInputSpec p it (by
    and_intros
    · grind
    · grind
    · simp_all
    · grind)
  simp [wp, Id.run] at ha
  split
  · split
    · split
      · expose_names
        split at heq
        · expose_names
          split at heq_2 <;> simp_all
        · expose_names
          split at heq_2
          · simp_all
          · grind
      · expose_names
        have := getPositionResultEqOk s
        grind
    · grind
  · grind

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
        have := anyTokenrespectsPosition σ τ it
        grind
    . split <;> grind
  · have ht := anyTokenEndOfInputSpec _ _ it (by grind only [= SPred.down_pure])
    simp [wp, Id.run] at ht
    have hn := notFollowedByEndOfInputSpec anyToken it  (by
      and_intros
      · grind
      · grind
      · intro it
        have := anyTokenrespectsPosition σ τ it
        grind
      · grind)
    simp [wp, Id.run] at hn
    simp_all
    rfl
