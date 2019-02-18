/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import fin.choice
import .basic .subst .mod .prf

universe u
variables {σ : Type u} {sig : σ → ℕ} {I : Type*} (ax : I → eqn sig)
include sig ax

lemma proof.sound {α : Type*} (a : alg sig α) (ha : ∀ i, sat a (ax i)) :
∀ {t u : term sig}, proof ax t u → (a ⊧ t ≡ u)
| ._ ._ (proof.axm ax i sub) val :=
  let val' := λ n, eval a val (sub n) in
  calc
  eval a val (subst sub ((ax i).fst))
      = eval a val' ((ax i).fst)            : by rw subst_eval
  ... = eval a val' ((ax i).snd)            : by rw ha i val' 
  ... = eval a val (subst sub ((ax i).snd)) : by rw subst_eval
| (term.var .(n)) (term.var .(n)) (proof.var ax n) val := rfl
| (term.app .(s) ts) (term.app .(s) us) (proof.app s ps) val :=
  have tup.map (eval a val) ts = tup.map (eval a val) us,
  from tup.ext (λ i, proof.sound (ps i) val),
  calc
  eval a val (term.app s ts) 
      = a.app s (tup.map (eval a val) ts) : by rw eval_app
  ... = a.app s (tup.map (eval a val) us) : by rw this
  ... = eval a val (term.app s us)        : by rw eval_app
| .(t) .(u) (proof.euc t u v ptv puv) val :=
  calc
  eval a val t
      = eval a val v : by rw proof.sound ptv val
  ... = eval a val u : by rw proof.sound puv val

theorem soundness {{t u : term sig}} : (ax ⊢ t ≡ u) → (ax ⊨ t ≡ u) := 
λ p _ a ha, proof.sound ax a ha p
