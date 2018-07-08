/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import uniq.inverse
import .basic .use

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

lemma hom_eval_use {f : α → β} (hf : hom a b f) (t : term sig) (val : α ^ (use t)) : 
f (eval_use a t val) = eval_use b t (tup.map f val) :=
let x := eval_use a t val in
let val' := tup.extend val (eval_use a t val) in
have tup.bar (λ n, f (val' n)) (use t) = tup.map f val,
from tup.ext (λ ⟨i,hi⟩, 
  calc
  (tup.bar (λ n, f (val' n)) (use t))[⟨i,hi⟩]
      = f (tup.extend val (eval_use a t val) i) : by rw tup.bar_val
  ... = f (val[⟨i,hi⟩]) : by rw tup.extend_of_lt hi
  ... = (tup.map f val)[⟨i,hi⟩] : rfl),
calc
f (eval_use a t val) 
    = f (eval_use a t (tup.bar val' (use t))) : by rw tup.bar_extend
... = f (eval a val' t) : by rw eval_use_eq_eval
... = eval b (λ n, f (val' n)) t : by rw hom_eval hf
... = eval_use b t (tup.bar (λ n, f (val' n)) (use t)) : by rw eval_use_eq_eval
... = eval_use b t (tup.map f val) : by rw this


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

lemma hom_sat_injective {f : α → β} (hf : hom a b f) (hi : function.injective f) :
∀ (e : eqn sig), (b ⊧ e) → (a ⊧ e) := 
λ e hb val, let val' := λ n, f (val n) in hi $
calc
f (eval a val e.fst) 
    = eval b val' e.fst  : by rw hom_eval hf
... = eval b val' e.snd    : by rw hb
... = f (eval a val e.snd) : by rw hom_eval hf

lemma hom_sat_use_surjective {f : α → β} (hf : hom a b f) (hs : function.surjective f) :
∀ (e : eqn sig), (sat_use a e) → (sat_use b e) := 
λ e ha val, let m := max (use e.fst) (use e.snd) in
have ∃ (val' : α ^ m), ∀ (i : fin m), f val'[i] = val[i],
from tup.choice (λ i, hs val[i]),
exists.elim this $ λ val' hv,
have tup.map f val' = val, from tup.ext hv,
calc
eval_use_of_le b val (e.fst) (le_max_left _ _) 
    = eval_use_of_le b (tup.map f val') (e.fst) (le_max_left _ _) : by rw this
... = f (eval_use_of_le a val' e.fst (le_max_left _ _)) : by rw hom_eval_use hf
... = f (eval_use_of_le a val' e.snd (le_max_right _ _)) : by rw ha
... = eval_use_of_le b (tup.map f val') e.snd (le_max_right _ _) : by rw hom_eval_use hf
... = eval_use_of_le b val (e.snd) (le_max_right _ _) : by rw this

lemma hom_sat_surjective {f : α → β} (hf : hom a b f) (hs : function.surjective f) :
∀ (e : eqn sig), (a ⊧ e) → (b ⊧ e) := 
λ e ha, sat_iff_sat_use.mpr (hom_sat_use_surjective hf hs e (sat_iff_sat_use.mp ha))

lemma hom_sat_bijective {f : α → β} (hf : hom a b f) (h : function.bijective f) :
∀ (e : eqn sig), (a ⊧ e) ↔ (b ⊧ e) := 
λ e, ⟨hom_sat_surjective hf h.right e, hom_sat_injective hf h.left e⟩

end

