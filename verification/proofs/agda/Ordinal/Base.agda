{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Stage S0 of docs/buchholz-plan.adoc.
--
-- A toy ordinal-term type, kept deliberately minimal so the first
-- closure proofs (see Ordinal.Closure) are not blocked on decidable
-- ordinal comparison. Nothing in this module asserts any ordinal
-- semantics: `OT` is pure syntax, and `psi` is a single pedagogical
-- constructor, not yet a Buchholz family `ψ_ν`.

module Ordinal.Base where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

data OT : Set where
  zero  : OT
  omega : OT
  plus  : OT → OT → OT
  psi   : OT → OT

-- Named atoms used by later modules as witnesses that the syntax is
-- populated and non-trivial.

one : OT
one = psi zero

ω^ω : OT
ω^ω = psi omega

-- Structural inequalities by clash of constructors (no K needed).

zero≢omega : zero ≢ omega
zero≢omega ()

zero≢one : zero ≢ one
zero≢one ()

omega≢one : omega ≢ one
omega≢one ()

psi-injective : ∀ {α β} → psi α ≡ psi β → α ≡ β
psi-injective refl = refl
