{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- Least-gap shape for the Buchholz ψ_ν constructor, mirroring the
-- pedagogical `psi-notin-C` / `psi-at-1` / `psi-least` triple in
-- `Ordinal.PsiSimple` but parameterised by the Ω-index ν.

module Ordinal.Buchholz.Psi where

open import Data.Nat.Base using (ℕ; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)

open import Ordinal.OmegaMarkers using (OmegaIndex; _≤Ω_)
open import Ordinal.Buchholz.Syntax using (BT; bpsi)
open import Ordinal.Buchholz.Closure using (Cν; cν-psi; cν-psi-index; cν-psi-decompose)

psiν-notin-Cν : ∀ {ν μ β} → ¬ Cν ν 0 (bpsi μ β)
psiν-notin-Cν (cν-psi _ () _)

-- Useful companion: any derivation of `ψ_μ β` lives at stage at least 1.

psiν-stage-lb : ∀ {ν μ β m} → Cν ν m (bpsi μ β) → 1 ≤ m
psiν-stage-lb (cν-psi _ k<m _) = ≤-trans (s≤s z≤n) k<m

psiν-index-bound : ∀ {ν μ β m} → Cν ν m (bpsi μ β) → μ ≤Ω ν
psiν-index-bound = cν-psi-index

-- Constructive entry (analogue of `psi-at-1`): once `β` is generable
-- at stage `k` and the Ω-index side-condition `μ ≤Ω ν` holds,
-- `bpsi μ β` enters the closure one stage later.

psiν-at-succ : ∀ {ν μ β k} → μ ≤Ω ν → Cν ν k β → Cν ν (suc k) (bpsi μ β)
psiν-at-succ μ≤ν ck = cν-psi μ≤ν ≤-refl ck

-- Least-gap shape (analogue of `psi-least`): any stage `m` that
-- derives `bpsi μ β` decomposes into a strictly earlier stage `k`
-- (i.e. `suc k ≤ m`) at which `β` was already derivable. Paired with
-- `psiν-at-succ` this pins the minimal entry stage of `bpsi μ β` at
-- exactly one above the minimal entry stage of its argument.

psiν-least-gap : ∀ {ν μ β m} → Cν ν m (bpsi μ β) → Σ ℕ (λ k → (suc k ≤ m) × Cν ν k β)
psiν-least-gap = cν-psi-decompose
