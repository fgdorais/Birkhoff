/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import uniq.inverse
import .basic

universe u
variables {σ : Type u} {sig : σ → ℕ} {α : Type*} {β : Type*} {γ : Type*}
include sig

structure hom (a : alg sig α) (b : alg sig β) (f : α → β) : Prop := 
(app : ∀ (s : σ) (xs : α ^ (sig s)), f (a.app s xs) = b.app s (tup.map f xs))

section
variables {a : alg sig α} {b : alg sig β} {c : alg sig γ}

lemma hom_app {f : α → β} (hf : hom a b f) :
∀ (s : σ) {xs : α ^ (sig s)}, f (a.app s xs) = b.app s (tup.map f xs) := hf.app

lemma hom_eval {f : α → β} (hf : hom a b f) :
∀ (t : term sig) (val : ℕ → α), f (eval a val t) = eval b (λ n, f (val n)) t
| (term.var n) val := rfl
| (term.app s ts) val :=
  let fval := λ n, f (val n) in 
  have tup.map f (tup.map (eval a val) ts) = tup.map (eval b fval) ts,
  from tup.ext (λ i, hom_eval (ts i) val),
  calc
  f (eval a val (term.app s ts))
      = f (a.app s (tup.map (eval a val) ts))         : by rw eval_app
  ... = b.app s (tup.map f (tup.map (eval a val) ts)) : by rw hom_app hf
  ... = b.app s (tup.map (eval b fval) ts)            : by rw this
  ... = eval b fval (term.app s ts)                   : by rw eval_app

lemma hom_comp {g : β → γ} {f : α → β} (hg : hom b c g) (hf : hom a b f) :
hom a c (g ∘ f) := {app := λ s xs, by simp [hf.app, hg.app]}

lemma hom_inverse {g : β → α} {f : α → β} (hf : hom a b f) (h : function.inverse g f) :
hom b a g :=
{ app := λ s xs,
  have hl : function.left_inverse g f, from function.left_inverse_of_inverse h,
  have hr : function.right_inverse g f, from function.right_inverse_of_inverse h,
  calc
  g (b.app s xs)
      = g (b.app s (tup.map id xs))            : rfl
  ... = g (b.app s (tup.map (f ∘ g) xs))       : by rw function.id_of_right_inverse hr
  ... = g (b.app s (tup.map f (tup.map g xs))) : by rw tup.map_map
  ... = g (f (a.app s (tup.map g xs)))         : by rw hf.app
  ... = a.app s (tup.map g xs)                 : by rw hl
}

end

