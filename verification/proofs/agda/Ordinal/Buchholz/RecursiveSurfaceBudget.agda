{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Budgeted recursive-surface descent.
--
-- Each recursive same-binder step consumes a finite amount of budget
-- determined by the depth of the direct recursive derivation. This
-- exposes a well-founded carrier for the recursive surface route even
-- before the final unbudgeted well-foundedness theorem is available.

module Ordinal.Buchholz.RecursiveSurfaceBudget where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Induction as NatInd using (<-wellFounded)
open import Data.Nat.Properties using (+-suc; m≤m+n)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (_on_)
open import Induction.WellFounded using (WellFounded; wf⇒asym; module Subrelation)
open import Relation.Binary.Construct.On as On using (wellFounded)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (¬_)

open import Ordinal.Buchholz.Syntax using (BT)
open import Ordinal.Buchholz.IteratedExtendedOrder using
  ( LiftedOrder
  ; LiftedOrder-lift
  )
open import Ordinal.Buchholz.RecursiveSurfaceOrder using
  ( _<ᵇʳᶠ_
  ; <ᵇʳᶠ-depth
  ; <ᵇʳᶠ⇒lifted
  )

BudgetedBT : Set
BudgetedBT = ℕ × BT

infix 4 _<ᵇʳᶠᵇ_

data _<ᵇʳᶠᵇ_ : BudgetedBT → BudgetedBT → Set where
  spend : ∀ {n x y} (p : x <ᵇʳᶠ y) → (n , x) <ᵇʳᶠᵇ (suc (n + <ᵇʳᶠ-depth p) , y)

BudgetOrder : Rel BudgetedBT _
BudgetOrder = _<_ on proj₁

<ᵇʳᶠᵇ⇒budget : _<ᵇʳᶠᵇ_ ⇒ BudgetOrder
<ᵇʳᶠᵇ⇒budget (spend {n} p) = m≤m+n (suc n) (<ᵇʳᶠ-depth p)

wf-<ᵇʳᶠᵇ : WellFounded _<ᵇʳᶠᵇ_
wf-<ᵇʳᶠᵇ =
  let module SR = Subrelation <ᵇʳᶠᵇ⇒budget
  in SR.wellFounded (On.wellFounded proj₁ NatInd.<-wellFounded)

<ᵇʳᶠᵇ-irreflexive : ∀ {s} → ¬ (s <ᵇʳᶠᵇ s)
<ᵇʳᶠᵇ-irreflexive {s} p = wf⇒asym wf-<ᵇʳᶠᵇ p p

LiftedOrder-raise-by
  : ∀ (k : ℕ) {n x y}
  → LiftedOrder n x y
  → LiftedOrder (k + n) x y
LiftedOrder-raise-by zero    p = p
LiftedOrder-raise-by (suc k) {n} p =
  LiftedOrder-lift (k + n) (LiftedOrder-raise-by k p)

<ᵇʳᶠᵇ⇒lifted : ∀ {sx sy} → sx <ᵇʳᶠᵇ sy → LiftedOrder (proj₁ sy) (proj₂ sx) (proj₂ sy)
<ᵇʳᶠᵇ⇒lifted {sx = n , x} {sy = .(suc (n + <ᵇʳᶠ-depth p)) , y} (spend {n} {x} {y} p) =
  subst (λ t → LiftedOrder t x y)
    (+-suc n (<ᵇʳᶠ-depth p))
    (LiftedOrder-raise-by n (<ᵇʳᶠ⇒lifted p))
