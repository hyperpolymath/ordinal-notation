{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Binary Veblen — RUNG 8: the generic fixed-point engine is MONOTONE IN
-- ITS ITERATED FUNCTION.  Target-side climb toward ψ₀(Ω_ω) (BH order-type
-- fidelity, open problem D-2026-06-14).  Builds on `VeblenBinary` (the
-- engine) and `VeblenBinaryNormal` (`nextFix-mono` — monotone in the
-- base).  2026-06-21.
--
-- ## What this slice adds
--
-- The engine's monotonicity was known in the BASE argument (`nextFix-mono`,
-- `deriv-mono`).  The missing axis is monotonicity in the iterated FUNCTION
-- `g` itself: a pointwise-smaller (continuous) function has a pointwise-
-- smaller fixed-point enumeration.
--
--   * `g-tower-mono-in-g` — `g ≤ h` pointwise (and `h` monotone) ⇒ the
--     iteration towers are ordered at every index.
--   * `nextFix-mono-in-g` — hence `nextFix g x ≤′ nextFix h x`.
--   * `deriv-mono-in-g`   — hence `deriv g β ≤′ deriv h β` for every β
--     (osuc case also uses `nextFix-mono` in the base).
--
-- This is the engine-side tool that *general first-argument monotonicity*
-- of `φ` (`a ≤′ b ⇒ φ_a x ≤′ φ_b x`) and the Γ₀ diagonal-closure
-- (`commonStep (n ↦ φ_{Γ-tower n}) Γ₀ ≤′ Γ₀`, the obligation
-- `VeblenBinaryLeast.Γ₀-fixed-from-closure` reduces the reverse Γ₀ fixed
-- point to) are built from: when one level's defining function dominates
-- another's, their `deriv` enumerations are ordered.
--
-- ## Honest scope (the Γ₀ fixed point is NOT closed here)
--
-- These are unconditional engine lemmas.  They do NOT by themselves close
-- `φ_Γ₀(0) ≤′ Γ₀`.  That closure is a COUPLED CLUSTER — it additionally
-- needs (i) level-inflationarity `α <′ φ_α(0)`, (ii) strict Γ-tower
-- monotonicity (from i), (iii) the general level-fixed-point
-- `a <′ b ⇒ φ_a(φ_b(y)) ≤′ φ_b(y)` (a value of a higher level is a fixed
-- point of every lower level), and (iv) general first-argument
-- monotonicity — which are mutually entangled and have delicate
-- degenerate-`olim` cases under the recursive `_≤′_`.  This slice supplies
-- the engine-monotonicity axis (iv's engine half); the rest remains the
-- open frontier.  Order-type fidelity ψ₀(Ω_ω) REMAINS OPEN
-- (D-2026-06-14).  No postulate is closed.  bi-`≤′` throughout.

module Ordinal.Brouwer.VeblenBinaryMonoG where

open import Data.Nat.Base using (ℕ; zero; suc)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13
  using (_≤′_; ≤′-refl; ≤′-trans; ≤′-lim; f-in-lim′)
open import Ordinal.Brouwer.VeblenBinary using (g-tower; nextFix; deriv)
open import Ordinal.Brouwer.VeblenBinaryNormal using (nextFix-mono)

----------------------------------------------------------------------
-- The iteration tower is monotone in the iterated function.
--
-- With `g y ≤′ h y` everywhere and `h` monotone, each tower step keeps
-- the order: `g-tower g x (suc n) = g (g-tower g x n) ≤′ h (g-tower g x n)`
-- [pointwise] `≤′ h (g-tower h x n) = g-tower h x (suc n)` [h monotone on
-- the IH].
----------------------------------------------------------------------

g-tower-mono-in-g :
  (g h : Ord → Ord)
  (g≤h : ∀ y → g y ≤′ h y)
  (h-mono : ∀ {a b} → a ≤′ b → h a ≤′ h b)
  (x : Ord) → ∀ n → g-tower g x n ≤′ g-tower h x n
g-tower-mono-in-g g h g≤h h-mono x zero    = ≤′-refl {x}
g-tower-mono-in-g g h g≤h h-mono x (suc n) =
  ≤′-trans {g (g-tower g x n)} {h (g-tower g x n)} {h (g-tower h x n)}
    (g≤h (g-tower g x n))
    (h-mono {g-tower g x n} {g-tower h x n} (g-tower-mono-in-g g h g≤h h-mono x n))

----------------------------------------------------------------------
-- nextFix is monotone in the iterated function.
--
-- `nextFix g x = olim (g-tower g (osuc x))`; `olim T ≤′ olim S` unfolds to
-- `∀ n → T n ≤′ olim S`, discharged per index by the tower order above
-- routed through `≤′-lim`.
----------------------------------------------------------------------

nextFix-mono-in-g :
  (g h : Ord → Ord)
  (g≤h : ∀ y → g y ≤′ h y)
  (h-mono : ∀ {a b} → a ≤′ b → h a ≤′ h b)
  (x : Ord) → nextFix g x ≤′ nextFix h x
nextFix-mono-in-g g h g≤h h-mono x = λ n →
  ≤′-lim {g-tower g (osuc x) n} (g-tower h (osuc x)) n
    (g-tower-mono-in-g g h g≤h h-mono (osuc x) n)

----------------------------------------------------------------------
-- deriv is monotone in the iterated function.
--
-- Structural recursion on β.  The `osuc` case composes monotonicity in
-- the function (`nextFix-mono-in-g` at the smaller base `deriv g β`) with
-- monotonicity in the base (`nextFix-mono h` along the IH); the `olim`
-- case is branchwise through `≤′-lim`.
----------------------------------------------------------------------

deriv-mono-in-g :
  (g h : Ord → Ord)
  (g≤h : ∀ y → g y ≤′ h y)
  (h-mono : ∀ {a b} → a ≤′ b → h a ≤′ h b)
  (β : Ord) → deriv g β ≤′ deriv h β
deriv-mono-in-g g h g≤h h-mono oz       = nextFix-mono-in-g g h g≤h h-mono oz
deriv-mono-in-g g h g≤h h-mono (osuc β) =
  ≤′-trans {nextFix g (deriv g β)} {nextFix h (deriv g β)} {nextFix h (deriv h β)}
    (nextFix-mono-in-g g h g≤h h-mono (deriv g β))
    (nextFix-mono h h-mono {deriv g β} {deriv h β}
      (deriv-mono-in-g g h g≤h h-mono β))
deriv-mono-in-g g h g≤h h-mono (olim k) = λ n →
  ≤′-lim {deriv g (k n)} (λ m → deriv h (k m)) n
    (deriv-mono-in-g g h g≤h h-mono (k n))
