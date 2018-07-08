/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .subst

universe u
variables {σ : Type u} {sig : σ → ℕ} {I : Type*} (ax : I → eqn sig)
include sig ax

definition models (e : eqn sig) : Prop :=
∀ {α : Type (u+1)} (a : alg sig α), (∀ i, a ⊧ ax i) → (a ⊧ e)

infix ` ⊨ `:20 := models

lemma mod_axiom (i : I) : ax ⊨ ax i := λ _ _ ha, ha i

lemma mod_reflexivity (t : term sig) : ax ⊨ t ≡ t :=
λ _ _ _ _, rfl

lemma mod_symmetry {{t u : term sig}} : (ax ⊨ t ≡ u) → (ax ⊨ u ≡ t) :=
λ h _ a ha val, eq.symm (h a ha val)

lemma mod_transitivity {{t u v : term sig}} : (ax ⊨ t ≡ u) → (ax ⊨ u ≡ v) → (ax ⊨ t ≡ v) :=
λ htu huv α a ha val, eq.trans (htu a ha val) (huv a ha val)

lemma mod_substitiution (sub : ℕ → term sig) {{t u : term sig}} :
(ax ⊨ t ≡ u) → (ax ⊨ subst sub t ≡ subst sub u) :=
λ h _ a ha val, 
calc
eval a val (subst sub t) 
    = eval a (λ n, eval a val (sub n)) t  : by rw subst_eval
... = eval a (λ n, eval a val (sub n)) u  : by rw h a ha
... = eval a val (subst sub u)            : by rw subst_eval

lemma mod_replacement {{sub₁ sub₂ : ℕ → term sig}} :
(∀ n, ax ⊨ (sub₁ n) ≡ (sub₂ n)) → (∀ t, ax ⊨ subst sub₁ t ≡ subst sub₂ t)
| h (term.var n) := 
  λ _ a ha val, h n a ha val
| h (term.app s ts) :=
  λ _ a ha val,
  have tup.map (eval a val) (tup.map (subst sub₁) ts) = tup.map (eval a val) (tup.map (subst sub₂) ts),
  from tup.ext (λ i, mod_replacement h (ts i) a ha val), 
  calc 
  eval a val (subst sub₁ (term.app s ts))
      = eval a val (term.app s (tup.map (subst sub₁) ts)) : by rw subst_app
  ... = a.app s (tup.map (eval a val) (tup.map (subst sub₁) ts)) : by rw eval_app
  ... = a.app s (tup.map (eval a val) (tup.map (subst sub₂) ts)) : by rw this
  ... = eval a val (term.app s (tup.map (subst sub₂) ts)) : by rw eval_app
  ... = eval a val (subst sub₂ (term.app s ts)) : by rw subst_app
