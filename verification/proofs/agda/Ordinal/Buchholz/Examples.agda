{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- Small concrete Buchholz terms and closure witnesses used as smoke
-- examples while the full ordering/normal-form development is pending.

module Ordinal.Buchholz.Examples where

open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Ordinal.OmegaMarkers using
  ( Omega0
  ; Omega1
  ; Omegaω
  ; ≤Ω-refl
  ; Omega0≤Omega1
  ; Omega1≤Omegaω
  )
open import Ordinal.Buchholz.Syntax using (BT; bOmega; bpsi; psi0)
open import Ordinal.Buchholz.Closure using (Cν; cν-omega; cν-psi; Cν-index-monotone)
open import Ordinal.Buchholz.Psi using (psiν-notin-Cν; psiν-stage-lb)

bh-psi0-omega1 : BT
bh-psi0-omega1 = bpsi Omega0 (bOmega Omega1)

bh-psi0-omegaω : BT
bh-psi0-omegaω = bpsi Omega0 (bOmega Omegaω)

psi0-expands : psi0 (bOmega Omega1) ≡ bh-psi0-omega1
psi0-expands = refl

psi0-Omega1-target : BT
psi0-Omega1-target = bh-psi0-omega1

omega1-in-C1-at-0 : Cν Omega1 0 (bOmega Omega1)
omega1-in-C1-at-0 = cν-omega ≤Ω-refl

psi0-omega1-at-1-in-C1 : Cν Omega1 1 bh-psi0-omega1
psi0-omega1-at-1-in-C1 = cν-psi Omega0≤Omega1 (s≤s z≤n) omega1-in-C1-at-0

psi0-omega1-not-at-0-in-C1 : ¬ Cν Omega1 0 bh-psi0-omega1
psi0-omega1-not-at-0-in-C1 = psiν-notin-Cν

psi0-omega1-stage-lb-in-C1 : ∀ {m} → Cν Omega1 m bh-psi0-omega1 → 1 ≤ m
psi0-omega1-stage-lb-in-C1 = psiν-stage-lb

omega1-in-Cω-at-0 : Cν Omegaω 0 (bOmega Omega1)
omega1-in-Cω-at-0 = Cν-index-monotone Omega1≤Omegaω omega1-in-C1-at-0

psi0-omega1-at-1 : Cν Omegaω 1 bh-psi0-omega1
psi0-omega1-at-1 = Cν-index-monotone Omega1≤Omegaω psi0-omega1-at-1-in-C1

psi0-omega1-not-at-0 : ¬ Cν Omegaω 0 bh-psi0-omega1
psi0-omega1-not-at-0 = psiν-notin-Cν
