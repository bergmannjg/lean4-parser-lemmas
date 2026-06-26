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

open Lean Lean.Syntax Parser

open Std.Do

@[expose] public section

namespace Parser

/-! WP instance of SimpleParser σ τ -/

instance [Parser.Stream σ τ] : LawfulMonad (SimpleParser σ τ) where
  id_map := by
    intros
    simp [Functor.map, bind, pure]
    apply funext
    intros
    split <;> grind
  map_const := by intros; rfl
  seqLeft_eq := by
    intros
    simp [Functor.map, SeqLeft.seqLeft]
    apply funext
    intros
    simp [bind, pure, Seq.seq]
    split
    · split
      · split
        · split
          · expose_names; simp_all; rw [← heq_2.right]; grind
          · grind
        · grind
      · grind
    · grind
  seqRight_eq := by
    intros
    simp [Functor.map, SeqRight.seqRight]
    apply funext
    intros
    simp [bind, pure, Seq.seq]
    split
    · split
      · split
        · split
          · expose_names; simp_all; rw [← heq_2.right]; simp [id]; grind
          · grind
        · grind
      · grind
    · grind
  pure_seq := by simp [Seq.seq, Functor.map, pure, bind]
  bind_pure_comp := by simp [bind, Functor.map, pure]
  bind_map := by
    intros
    simp [Seq.seq, bind, pure, Functor.map]
    apply funext
    intros
    grind
  pure_bind := by simp [bind, pure]
  bind_assoc := by
    simp [bind, pure]
    intros
    apply funext
    intros
    grind

instance SimpleParser.instWP [Parser.Stream σ τ]
    : WP (SimpleParser σ τ) (.except (Parser.Error.Simple σ τ) (.arg σ .pure)) where
  wp x :=
    { trans := fun Q s => match x.run s with
        | .ok s' a => Q.1 a s'
        | .error s' e => Q.2.1 e s'
      conjunctiveRaw := by
        intro _ _
        apply SPred.bientails.of_eq
        ext s
        dsimp
        cases (x.run s) <;> simp
    }

instance SimpleParser.instWPMonad [Parser.Stream σ τ]
    : WPMonad (SimpleParser σ τ) (.except (Parser.Error.Simple σ τ) (.arg σ .pure)) where
  wp_pure a := by
    ext Q : 1; simp only [wp, PredTrans.apply, pure]; rfl
  wp_bind x f := by
    ext Q : 2
    simp only [wp, PredTrans.apply_Bind_bind, Parser.run]
    simp only [PredTrans.apply]
    simp only [bind, pure]
    grind

theorem SimpleParser.of_wp_run_eq {α} [Parser.Stream σ τ]
  {x : Parser.Result (Error.Simple σ τ) σ α} {prog : SimpleParser σ τ α} (h : Parser.run prog s = x)
  (P : Parser.Result (Error.Simple σ τ) σ α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a s' => ⌜P (Parser.Result.ok s' a)⌝,
                     fun e s' => ⌜P (Parser.Result.error s' e)⌝⟩ s) → P x := by
  intro hspec
  simp only [wp, PredTrans.apply] at hspec
  split at hspec
  case h_1 a s' heq => rw[← heq] at hspec; exact h ▸ hspec True.intro
  case h_2 e s' heq => rw[← heq] at hspec; exact h ▸ hspec True.intro

theorem SimpleParser.of_wp_eq [Parser.Stream σ τ] (x : SimpleParser σ τ α)
  {P : σ → SPred PostShape.pure.args} {Q : PostCond α (.except (Error.Simple σ τ) (.arg σ .pure))}
    (h : P ⊢ₛ wp⟦x⟧ Q) (it : σ) (hp : (P it).down)
    : (match x it with | .ok s a => Q.1 a s | .error s e => Q.2.1 e s).down := by
  simp [wp, PredTrans.apply, Parser.run] at h
  have := h it hp
  grind
