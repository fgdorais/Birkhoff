/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .hom .use

universe u
variables {σ : Type u} {sig : σ → ℕ}
include sig

class congruence {α : Type*} (a : alg sig α) extends setoid α :=
(app : ∀ (s : σ) (xs ys : α ^ (sig s)), (∀ i, r xs[i] ys[i]) → r (alg.app a s xs) (alg.app a s ys))

section
variables {α : Type*} (a : alg sig α) (c : congruence a)
include c

definition sat_congr (e : eqn sig) : Prop :=
∀ val : ℕ → α, eval a val e.fst ≈ eval a val e.snd

definition sat_congr_use (e : eqn sig) : Prop :=
∀ val : α ^ (max (use e.fst) (use e.snd)), eval_use_of_le a val e.fst (le_max_left _ _) ≈ eval_use_of_le a val e.snd (le_max_right _ _)

notation a ` ⊧ ` e ` mod ` c := sat_congr a c e

variables {a c}

lemma sat_congr_iff_sat_congr_use {e : eqn sig} :
(a ⊧ e mod c) ↔ sat_congr_use a c e :=
let m := max (use e.fst) (use e.snd) in
iff.intro
 (λ h val,
  let x := eval_use_of_le a val e.fst (le_max_left _ _) in
  calc
  eval_use_of_le a val e.fst (le_max_left _ _)
      = eval_use_of_le a (tup.bar (tup.extend val x) m) e.fst (le_max_left _ _) : by rw tup.bar_extend
  ... = eval a (tup.extend val x) e.fst : by rw eval_eq_eval_use_of_le
  ... ≈ eval a (tup.extend val x) e.snd : by apply h
  ... = eval_use_of_le a (tup.bar (tup.extend val x) m) e.snd (le_max_right _ _) : by rw eval_eq_eval_use_of_le
  ... = eval_use_of_le a val (e.snd) (le_max_right _ _) : by rw tup.bar_extend)
 (λ h val,
  calc
  eval a val e.fst 
      = eval_use_of_le a (tup.bar val m) e.fst (le_max_left _ _) : by rw eval_eq_eval_use_of_le
  ... ≈ eval_use_of_le a (tup.bar val m) e.snd (le_max_right _ _) : by apply h
  ... = eval a val e.snd : by rw eval_eq_eval_use_of_le)

variable (c)

definition quotient_alg : alg sig (quotient c.to_setoid) := 
{ app := 
  λ s, let f := λ xs, quotient.mk (a.app s xs) in
  have ∀ xs ys : α ^ (sig s), xs ≈ ys → f xs = f ys,
  from λ xs ys hxy, quotient.sound (congruence.app s xs ys hxy), 
  quotient.tup_lift f this
}

@[reducible]
definition quotient_map : 
α → quotient c.to_setoid := quotient.mk

definition quotient_hom : 
hom a (quotient_alg c) (quotient_map c) := 
{ app := λ s xs, eq.symm (quotient.tup_lift_beta _ _ xs)
}

definition quotient_app (s : σ) {xs : α ^ (sig s)} :
quotient_map c (a.app s xs) = (quotient_alg c).app s (tup.map (quotient_map c) xs) := 
hom_app (quotient_hom c) s

definition quotient_eval (t : term sig) (val : ℕ → α) :
quotient_map c (eval a val t) = eval (quotient_alg c) (λ n, quotient_map c (val n)) t :=
hom_eval (quotient_hom c) t val

theorem quotient_sound {{x y : α}} :
x ≈ y → quotient_map c x = quotient_map c y := quotient.sound

theorem quotient_exact {{x y : α}} : 
quotient_map c x = quotient_map c y → x ≈ y := quotient.exact

lemma quotient_sat_use_of_sat_congr_use {e : eqn sig} :
sat_congr_use a c e → sat_use (quotient_alg c) e :=
λ h qval,
have ∃ val, ∀ i, (quotient_map c) val[i] = qval[i],
from tup.choice (show ∀ i, ∃ x, quotient_map c x = qval[i], from λ i, quotient.exists_rep qval[i]),
exists.elim this $
λ val hval,
have tup.map (quotient_map c) val = qval,
from tup.ext hval,
calc
eval_use_of_le (quotient_alg c) qval (e.fst) (le_max_left _ _)
    = eval_use_of_le (quotient_alg c) (tup.map (quotient_map c) val) (e.fst) (le_max_left _ _) : by rw this
... = quotient_map c (eval_use_of_le a val e.fst (le_max_left _ _)) : by rw hom_eval_use (quotient_hom c)
... = quotient_map c (eval_use_of_le a val e.snd (le_max_right _ _)) : by rw quotient_sound c (h val)
... = eval_use_of_le (quotient_alg c) (tup.map (quotient_map c) val) (e.snd) (le_max_right _ _) : by rw hom_eval_use (quotient_hom c)
... = eval_use_of_le (quotient_alg c) qval (e.snd) (le_max_right _ _) : by rw this

theorem quotient_sat {e : eqn sig} :
(quotient_alg c ⊧ e) ↔ (a ⊧ e mod c) := 
⟨ λ h val, quotient_exact c $
  calc
  quotient_map c (eval a val e.fst) 
      = eval (quotient_alg c) (λ n, quotient_map c (val n)) e.fst : by rw hom_eval (quotient_hom c)
  ... = eval (quotient_alg c) (λ n, quotient_map c (val n)) e.snd : by rw h
  ... = quotient_map c (eval a val e.snd) : by rw hom_eval (quotient_hom c)
, λ h, sat_iff_sat_use.mpr $
  quotient_sat_use_of_sat_congr_use c $
  sat_congr_iff_sat_congr_use.mp h
⟩ 

end