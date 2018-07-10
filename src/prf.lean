/-
Copyright © 2018 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic .subst

universes u v 
variables {σ : Type u} {sig : σ → ℕ} {I : Type v} (ax : I → eqn sig)
include sig ax

inductive proof : term sig → term sig → Type (max (u+1) v)
| axm (i : I) (sub : ℕ → term sig) : proof (subst sub (ax i).fst) (subst sub (ax i).snd)
| var (n : ℕ) : proof (term.var n) (term.var n)
| app (s : σ) {ts us : term sig ^ (sig s)} : (Π i, proof ts[i] us[i]) → proof (term.app s ts) (term.app s us)  
| euc (t u v : term sig) : proof t v → proof u v → proof t u

@[reducible]
definition proves (e : eqn sig) := proof ax e.fst e.snd

infix ` ⊢ `:20 := proves

variable {ax}

definition prf_reflexivity : Π t : term sig, ax ⊢ t ≡ t
| (term.var n) := proof.var ax n
| (term.app s ts) := proof.app s (λ i, prf_reflexivity (ts i))

definition prf_symmetry {{t u : term sig}} : (ax ⊢ t ≡ u) → (ax ⊢ u ≡ t) :=
λ ptu, proof.euc u t u (prf_reflexivity u) ptu

definition prf_transitivity {{t u v : term sig}} : (ax ⊢ t ≡ u) → (ax ⊢ u ≡ v) → (ax ⊢ t ≡ v) :=
λ ptu puv, proof.euc t v u ptu (prf_symmetry puv)

definition prf_substitution (sub : ℕ → term sig) : 
Π {{t u : term sig}}, proof ax t u → proof ax (subst sub t) (subst sub u)
| ._ ._ (proof.axm ax i sub₀) :=
  have ht : subst (subst.comp sub₀ sub) (ax i).fst = subst sub (subst sub₀ (ax i).fst), by rw subst.subst_subst,
  have hu : subst (subst.comp sub₀ sub) (ax i).snd = subst sub (subst sub₀ (ax i).snd), by rw subst.subst_subst,
  eq.rec_on ht (eq.rec_on hu (proof.axm ax i (subst.comp sub₀ sub)))
| (term.var .(n)) (term.var .(n)) (proof.var ax n) := 
  prf_reflexivity (sub n)
| (term.app ._ ts) (term.app ._ us) (proof.app s ps) :=
  have ht : term.app s (tup.map (subst sub) ts) = subst sub (term.app s ts), by rw subst_app,
  have hu : term.app s (tup.map (subst sub) us) = subst sub (term.app s us), by rw subst_app,
  have Π i, ax ⊢ (subst sub ts[i]) ≡ (subst sub us[i]), from λ i, prf_substitution (ps i),
  eq.rec_on ht (eq.rec_on hu (proof.app s this))
| .(t) .(u) (proof.euc t u v htv huv) :=
  proof.euc (subst sub t) (subst sub u) (subst sub v) (prf_substitution htv) (prf_substitution huv)

definition prf_replacement {{sub₁ sub₂ : ℕ → term sig}} (h : Π n, ax ⊢ sub₁ n ≡ sub₂ n) :
Π (t : term sig), ax ⊢ subst sub₁ t ≡ subst sub₂ t
| (term.var n) := h n
| (term.app s ts) :=
  have h₁ : term.app s (tup.map (subst sub₁) ts) = subst sub₁ (term.app s ts), by rw subst_app, 
  have h₂ : term.app s (tup.map (subst sub₂) ts) = subst sub₂ (term.app s ts), by rw subst_app,
  eq.rec_on h₁ (eq.rec_on h₂ (proof.app s (λ i, prf_replacement (ts i))))

definition prf_translate {I' : Type*} {ax' : I' → eqn sig} (t : Π (i : I'), ax ⊢ (ax' i)) :
∀ {{t u : term sig}}, proof ax' t u → proof ax t u
| ._ ._ (proof.axm ax' i sub) := 
  prf_substitution sub (t i)
| ._ ._ (proof.var ax' n) := 
  proof.var ax n
| ._ ._ (proof.app s ps) := 
  proof.app s (λ i, prf_translate (ps i))
| ._ ._ (proof.euc t u v ptv puv) :=
  proof.euc t u v (prf_translate ptv) (prf_translate puv)
