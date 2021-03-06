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

namespace proof
variable {ax}

definition reflexivity : Π t : term sig, ax ⊢ t ≡ t
| (term.var n) := var ax n
| (term.app s ts) := app s (λ i, reflexivity (ts i))

definition symmetry {{t u : term sig}} : (ax ⊢ t ≡ u) → (ax ⊢ u ≡ t) :=
λ ptu, euc u t u (reflexivity u) ptu

definition transitivity {{t u v : term sig}} : (ax ⊢ t ≡ u) → (ax ⊢ u ≡ v) → (ax ⊢ t ≡ v) :=
λ ptu puv, euc t v u ptu (symmetry puv)

definition substitution (sub : ℕ → term sig) : 
Π {{t u : term sig}}, proof ax t u → proof ax (subst sub t) (subst sub u)
| ._ ._ (axm ax i sub₀) :=
  have ht : subst (subst.comp sub₀ sub) (ax i).fst = subst sub (subst sub₀ (ax i).fst), by rw subst.subst_subst,
  have hu : subst (subst.comp sub₀ sub) (ax i).snd = subst sub (subst sub₀ (ax i).snd), by rw subst.subst_subst,
  eq.rec_on ht (eq.rec_on hu (axm ax i (subst.comp sub₀ sub)))
| (term.var .(n)) (term.var .(n)) (var ax n) := 
  reflexivity (sub n)
| (term.app .(s) ts) (term.app .(s) us) (app s ps) :=
  have ht : term.app s (tup.map (subst sub) ts) = subst sub (term.app s ts), by rw subst_app,
  have hu : term.app s (tup.map (subst sub) us) = subst sub (term.app s us), by rw subst_app,
  have Π i, ax ⊢ (subst sub ts[i]) ≡ (subst sub us[i]), from λ i, substitution (ps i),
  eq.rec_on ht (eq.rec_on hu (app s this))
| .(t) .(u) (euc t u v htv huv) :=
  euc (subst sub t) (subst sub u) (subst sub v) (substitution htv) (substitution huv)

definition replacement {{sub₁ sub₂ : ℕ → term sig}} (h : Π n, ax ⊢ sub₁ n ≡ sub₂ n) :
Π (t : term sig), ax ⊢ subst sub₁ t ≡ subst sub₂ t
| (term.var n) := h n
| (term.app s ts) :=
  have h₁ : term.app s (tup.map (subst sub₁) ts) = subst sub₁ (term.app s ts), by rw subst_app, 
  have h₂ : term.app s (tup.map (subst sub₂) ts) = subst sub₂ (term.app s ts), by rw subst_app,
  eq.rec_on h₁ (eq.rec_on h₂ (app s (λ i, replacement (ts i))))

definition translate {I' : Type*} {ax' : I' → eqn sig} (p : Π (i : I'), ax ⊢ (ax' i)) :
∀ {{t u : term sig}}, proof ax' t u → proof ax t u
| ._ ._ (axm ax' i sub) := 
  substitution sub (p i)
| ._ ._ (var ax' n) := 
  var ax n
| ._ ._ (app s ps) := 
  app s (λ i, translate (ps i))
| ._ ._ (euc t u v ptv puv) :=
  euc t u v (translate ptv) (translate puv)

end proof