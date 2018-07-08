import .basic

variables {σ : Type*} {sig : σ → ℕ} {α : Type*}
include sig

definition use : term sig → ℕ
| (term.var n) := n+1
| (term.app s ts) :=
  if hs : sig s = 0 then 0
  else tup.max' hs (λ i, use (ts i))

lemma use_app {s : σ} {ts : term sig ^ (sig s)} (i : fin (sig s)) : 
use (ts i) ≤ use (term.app s ts) :=
if hs : sig s = 0 then
  fin.elim0 (eq.rec_on hs i)
else
  calc
  use (term.app s ts) 
      = tup.max' hs (tup.map use ts) : dif_neg hs
  ... ≥ (tup.map use ts)[i]          : tup.le_max'
  ... = use ts[i]                    : rfl

@[reducible]
definition eval_use (a : alg sig α) : Π (t : term sig), α ^ (use t) → α
| (term.var n) val := 
  val ⟨n, nat.lt_succ_self n⟩
| (term.app s ts) val := 
  a.app s (λ i, eval_use (ts i) (tup.take_of_le (use_app i) val))

lemma eval_use_eq_eval {a : alg sig α} {val : ℕ → α} : 
Π (t : term sig), eval_use a t (tup.bar val (use t)) = eval a val t
| (term.var n) := rfl
| (term.app s ts) := 
  let m := use (term.app s ts) in
  let valm := tup.bar val m in
  have ∀ i, tup.take_of_le (use_app i) valm = tup.bar val (use ts[i]), 
  from λ i, tup.take_bar val (use_app i),
  have ∀ i, 
  eval_use a ts[i] (tup.take_of_le (use_app i) valm)
  = eval_use a ts[i] (tup.bar val (use ts[i])),
  begin 
  intro i, 
  rw tup.take_bar val (use_app i)
  end,
  calc 
  eval_use a (term.app s ts) valm
      = a.app s (λ i, eval_use a ts[i] (tup.take_of_le (use_app i) valm)) : rfl
  ... = a.app s (λ i, eval_use a ts[i] (tup.bar val (use ts[i]))) : by rw tup.ext this
  ... = a.app s (λ i, eval a val ts[i]) : by rw tup.ext (λ i, eval_use_eq_eval (ts i))
  ... = eval a val (term.app s ts) : rfl

theorem eval_continuity {t : term sig} {a : alg sig α} {val₁ val₂ : ℕ → α} :
(∀ i < use t, val₁ i = val₂ i) → eval a val₁ t = eval a val₂ t :=
assume h,
have tup.bar val₁ (use t) = tup.bar val₂ (use t),
from tup.ext (λ ⟨i,hi⟩, h i hi),
calc
eval a val₁ t
    = eval_use a t (tup.bar val₁ (use t)) : by rw eval_use_eq_eval
... = eval_use a t (tup.bar val₂ (use t)) : by rw this
... = eval a val₂ t : by rw eval_use_eq_eval  

@[reducible]
definition eval_use_of_le (a : alg sig α) {n : ℕ} (val : α ^ n) (t : term sig) : 
use t ≤ n → α := λ h, eval_use a t (tup.take_of_le h val)

lemma eval_eq_eval_use_of_le {a : alg sig α} {val : ℕ → α} (t : term sig) {m : ℕ} {hm : use t ≤ m} :
eval a val t = eval_use_of_le a (tup.bar val m) t hm :=
calc
eval a val t
    = eval_use a t (tup.bar val (use t)) : by rw eval_use_eq_eval
... = eval_use a t (tup.take_of_le hm (tup.bar val m)) : by rw tup.take_bar
... = eval_use_of_le a (tup.bar val m) t hm : rfl

definition sat_use (a : alg sig α) (e : eqn sig) : Prop :=
∀ (val : α ^ max (use e.fst) (use e.snd)), eval_use_of_le a val e.fst (le_max_left _ _) = eval_use_of_le a val e.snd (le_max_right _ _)

lemma sat_iff_sat_use {a : alg sig α} {e : eqn sig} :
a ⊧ e ↔ sat_use a e :=
let m := max (use e.fst) (use e.snd) in iff.intro
 (λ h val, 
  let x := eval_use_of_le a val e.fst (le_max_left _ _) in
  calc
  eval_use_of_le a val e.fst (le_max_left _ _)
      = eval_use_of_le a (tup.bar (tup.extend val x) m) e.fst (le_max_left _ _) : by rw tup.bar_extend
  ... = eval a (tup.extend val x) e.fst : by rw eval_eq_eval_use_of_le
  ... = eval a (tup.extend val x) e.snd : by apply h
  ... = eval_use_of_le a (tup.bar (tup.extend val x) m) e.snd (le_max_right _ _) : by rw eval_eq_eval_use_of_le
  ... = eval_use_of_le a val (e.snd) (le_max_right _ _) : by rw tup.bar_extend)
 (λ h val,  
  calc
  eval a val e.fst 
      = eval_use_of_le a (tup.bar val m) e.fst (le_max_left _ _) : by rw eval_eq_eval_use_of_le
  ... = eval_use_of_le a (tup.bar val m) e.snd (le_max_right _ _) : by apply h
  ... = eval a val e.snd : by rw eval_eq_eval_use_of_le)

