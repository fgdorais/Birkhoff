/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import fin.choice
import .basic .subst .congr .mod .prf

universe u
variables {σ : Type u} {sig : σ → ℕ} {I : Type*} (ax : I → eqn sig)
include sig ax

/-- soundness --/

lemma prf_sound {α : Type*} (a : alg sig α) (ha : ∀ i, sat a (ax i)) :
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
  from tup.ext (λ i, prf_sound (ps i) val),
  calc
  eval a val (term.app s ts) 
      = a.app s (tup.map (eval a val) ts) : by rw eval_app
  ... = a.app s (tup.map (eval a val) us) : by rw this
  ... = eval a val (term.app s us)        : by rw eval_app
| .(t) .(u) (proof.euc t u v ptv puv) val :=
  calc
  eval a val t
      = eval a val v : by rw prf_sound ptv val
  ... = eval a val u : by rw prf_sound puv val

theorem soundness {{t u : term sig}} : (ax ⊢ t ≡ u) → (ax ⊨ t ≡ u) := 
λ p _ a ha, prf_sound ax a ha p

/-- completeness --/

instance prf_congr : congruence (term_alg sig) := 
{ r := λ t u, nonempty (proof ax t u)
, iseqv := 
  mk_equivalence _ 
    (λ t, ⟨prf_reflexivity t⟩) 
    (λ t u ⟨ptu⟩, ⟨prf_symmetry ptu⟩)
    (λ t u v ⟨ptu⟩ ⟨puv⟩, ⟨prf_transitivity ptu puv⟩),
  app := λ s ts us h,
  have nonempty (Π i : fin (sig s), proof ax (ts i) (us i)), 
  from fin.choice h,
  nonempty.elim this (λ ps, ⟨proof.app s ps⟩)
}

lemma prf_congr_ax (i : I) : quotient_alg (prf_congr ax) ⊧ ax i :=
(quotient_sat (prf_congr ax)).mpr $
λ sub, ⟨proof.axm ax i sub⟩

lemma prf_exact {t u : term sig} : 
(quotient_alg (prf_congr ax) ⊧ t ≡ u) → nonempty (ax ⊢ t ≡ u) := 
assume h,
let c := prf_congr ax in
let val := λ n, quotient_map c (term.var n) in 
have quotient_map c t = quotient_map c u, 
from calc
quotient_map c t
    = quotient_map c (subst subst.ident t) : by rw subst.subst_ident
... = eval (quotient_alg c) val t : by rw hom_eval (quotient_hom c)
... = eval (quotient_alg c) val u : h val
... = quotient_map c (subst subst.ident u) : by rw hom_eval (quotient_hom c)
... = quotient_map c u : by rw subst.subst_ident,
quotient_exact (prf_congr ax) this

theorem completeness {{t u : term sig}} : (ax ⊨ t ≡ u) → nonempty (ax ⊢ t ≡ u) :=
assume h, prf_exact ax (h (quotient_alg (prf_congr ax)) (prf_congr_ax ax))
