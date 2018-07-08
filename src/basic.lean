/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tup

universes u v
variables {σ : Type u} (sig : σ → ℕ) (α : Type v)
include sig

inductive term : Type (u+1)
| var {} : ℕ → term
| app (s : σ) : term ^ (sig s) → term

structure eqn : Type (u+1) := (fst snd : term sig)

infix ≡ := eqn.mk

structure alg : Type (max u v) := 
(app : Π (s : σ), α ^ (sig s) → α)

definition term_alg : alg sig (term sig) := 
{ app := term.app
}

definition eqn_alg : alg sig (eqn sig) := 
{ app := λ s es, term.app s (tup.map eqn.fst es) ≡ term.app s (tup.map eqn.snd es)
}

variables {sig} {α} (a : alg sig α)

definition eval (val : ℕ → α) : term sig → α
| (term.var n) := val n
| (term.app s ts) := alg.app a s (λ i, eval (ts i))

@[simp]
lemma eval_var (val : ℕ → α) {n : ℕ} : 
eval a val (term.var n) = val n := rfl

@[simp]
lemma eval_app (val : ℕ → α) (s : σ) {ts : term sig ^ (sig s)} : 
eval a val (term.app s ts) = alg.app a s (tup.map (eval a val) ts) := rfl

definition sat (e : eqn sig) : Prop :=
∀ val : ℕ → α, eval a val e.fst = eval a val e.snd

infix ` ⊧ `:20 := sat