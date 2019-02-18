/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .subst .congr .mod .prf

universe u
variables {σ : Type u} {sig : σ → ℕ} {I : Type*} (ax : I → eqn sig)
include sig ax

instance prf_congr : congruence (term_alg sig) := 
{ r := λ t u, nonempty (proof ax t u)
, iseqv := 
  mk_equivalence _ 
    (λ t, ⟨proof.reflexivity t⟩) 
    (λ t u ⟨ptu⟩, ⟨proof.symmetry ptu⟩)
    (λ t u v ⟨ptu⟩ ⟨puv⟩, ⟨proof.transitivity ptu puv⟩),
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
