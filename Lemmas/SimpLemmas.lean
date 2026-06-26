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

open Lean Lean.Syntax Parser

open Std.Do

@[expose] public section

namespace Parser

/-! Simp lemmas for SimpleParser σ τ -/

@[grind .] theorem SimpleParser.getPosition_eq_ok [Parser.Stream σ τ] (it : σ)
    : (getPosition : SimpleParser σ τ _) it = Result.ok it (Stream.getPosition it) := by
  simp [getPosition, Functor.map]
  rfl

@[simp] theorem setPosition_eq_ok  [Parser.Stream σ τ] (s1 : σ) (p : Stream.Position σ)
    : ∃ (s2 : σ), (setPosition p : SimpleParser σ τ Unit) s1 = Result.ok s2 () :=
  Exists.intro (Stream.setPosition s1 p) rfl

@[simp] theorem SimpleParser.throw_eq_error [Parser.Stream σ τ] (it : σ) (e : Error.Simple σ τ)
    : (MonadExcept.throw e : SimpleParser σ τ α) it = Result.error it e := by
  simp [throw, throwThe, MonadExceptOf.throw, pure]

@[simp, grind .] theorem throwUnexpected_eq_error [Parser.Stream σ τ]
    (α : Type) (s : σ) (c : Option τ)
    : (throwUnexpected c s : Id (Parser.Result (Error.Simple σ τ) σ α))
      = Result.error s (Error.unexpected (Stream.getPosition s) c) := by
  simp only [throwUnexpected, bind, throw, throwThe, MonadExceptOf.throw, pure]
  rfl

@[simp] theorem SimpleParser.WP.seqRight (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (q : SimpleParser σ τ β)
  {Q : PostCond β (.except (Error.Simple σ τ) (.arg σ .pure))}
    : wp⟦p *> q⟧ Q = wp⟦p⟧ (fun _ => wp⟦q⟧ Q, Q.2) := by
  simp [wp, SeqRight.seqRight, PredTrans.apply, Parser.run, bind, pure]
  funext
  grind

@[simp] theorem SimpleParser.WP.tryCatch (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  (p : SimpleParser σ τ α) (h : (Error.Simple σ τ) → SimpleParser σ τ α)
  {Q : PostCond α (.except (Error.Simple σ τ) (.arg σ .pure))}
    : wp⟦MonadExceptOf.tryCatch p h⟧ Q
      = wp⟦p⟧ (Q.1, fun e => wp⟦h e⟧ Q, Q.snd.snd) := by
  simp [wp, MonadExceptOf.tryCatch, PredTrans.apply, pure, bind, ParserT.run, Parser.run]
  funext
  grind

@[simp] theorem SimpleParser.WP.throwErrorWithMessage (σ τ : Type) [Parser.Stream σ τ] [Stream.Remaining σ]
  [Stream.ValidPosition σ] [Stream.RespectsPosition σ τ]
  (e : Error.Simple σ τ) (msg : String)
  {Q : PostCond α (.except (Error.Simple σ τ) (.arg σ .pure))}
    : wp⟦(throwErrorWithMessage e msg : SimpleParser σ τ α)⟧ Q
      = fun s => Q.2.1 (Error.addMessage e (Stream.getPosition s) msg) s := by
  simp [wp, PredTrans.apply, Parser.throwErrorWithMessage, Parser.run, bind, pure]
  funext
  split
  · rename_i heq
    split at heq <;> simp_all
  · rename_i heq
    grind
