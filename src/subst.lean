/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .hom

universe u
variables {σ : Type u} {sig : σ → ℕ}
include sig

@[reducible]
definition subst (sub : ℕ → term sig) : term sig → term sig :=
eval (term_alg sig) sub

definition subst_app (sub : ℕ → term sig) (s : σ) {ts : term sig ^ (sig s)} :
subst sub (term.app s ts) = term.app s (tup.map (subst sub) ts) :=
eval_app (term_alg sig) sub s

definition subst_hom (sub : ℕ → term sig) : 
hom (term_alg sig) (term_alg sig) (subst sub) := {app := subst_app sub}

lemma subst_eval {α : Type*} (a : alg sig α) {sub : ℕ → term sig} {val : ℕ → α} : 
∀ (t : term sig), eval a val (subst sub t) = eval a (λ n, eval a val (sub n)) t
| (term.var n) := rfl
| (term.app s ts) := 
  let val' := λ n, eval a val (sub n) in 
  have tup.map (eval a val) (tup.map (subst sub) ts) = tup.map (eval a val') ts,
  from tup.ext (λ i, subst_eval ts[i]),
  calc
  eval a val (subst sub (term.app s ts)) 
      = eval a val (term.app s (tup.map (subst sub) ts)) : by rw subst_app sub
  ... = a.app s (tup.map (eval a val) (tup.map (subst sub) ts)) : by rw eval_app a val
  ... = a.app s (tup.map (eval a val') ts) : by rw this
  ... = eval a val' (term.app s ts) : by rw eval_app a val'

namespace subst

@[reducible]
definition ident : ℕ → term sig := λ n, term.var n

@[reducible]
definition comp (sub₁ sub₂ : ℕ → term sig) : ℕ → term sig :=
λ n, subst sub₂ (sub₁ n)

lemma subst_ident : ∀ (t : term sig), subst ident t = t
| (term.var n) := rfl
| (term.app s ts) :=
  have tup.map (subst ident) ts = ts,
  from tup.ext (λ i, subst_ident (ts i)),
  calc
  subst ident (term.app s ts) 
      = term.app s (tup.map (subst ident) ts) : subst_app ident s
  ... = term.app s ts : by rw this

lemma subst_subst (sub₁ sub₂ : ℕ → term sig) 
: ∀ (t : term sig), subst sub₂ (subst sub₁ t) = subst (comp sub₁ sub₂) t
| (term.var n) := rfl
| (term.app s ts) :=
  have tup.map (subst sub₂) (tup.map (subst sub₁) ts) = tup.map (subst (comp sub₁ sub₂)) ts,
  from tup.ext (λ i, subst_subst ts[i]), 
  calc
  subst sub₂ (subst sub₁ (term.app s ts))
      = subst sub₂ (term.app s (tup.map (subst sub₁) ts)) : by rw subst_app sub₁
  ... = term.app s (tup.map (subst sub₂) (tup.map (subst sub₁) ts)) : by rw subst_app sub₂
  ... = term.app s (tup.map (subst (comp sub₁ sub₂)) ts) : by rw this
  ... = subst (comp sub₁ sub₂) (term.app s ts) : by rw subst_app (comp sub₁ sub₂)

lemma comp_assoc (sub₁ sub₂ sub₃ : ℕ → term sig) : 
comp (comp sub₁ sub₂) sub₃ = comp sub₁ (comp sub₂ sub₃) :=
funext (λ n, subst_subst sub₂ sub₃ (sub₁ n))

lemma comp_ident (sub : ℕ → term sig) :
comp sub ident = sub :=
funext (λ n, subst_ident (sub n))

lemma ident_comp (sub : ℕ → term sig) :
comp ident sub = sub :=
funext (λ n, rfl)

instance : monoid (ℕ → term sig) := 
{ mul := comp
, one := ident
, mul_assoc := comp_assoc
, mul_one := comp_ident
, one_mul := ident_comp
}

end subst


