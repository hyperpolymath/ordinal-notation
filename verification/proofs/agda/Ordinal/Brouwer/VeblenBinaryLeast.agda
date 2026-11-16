{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Binary Veblen — RUNG 7: the generic fixed-point engine is MINIMAL —
-- `nextFix g x` is the LEAST pre-fixed point of `g` strictly above `x`,
-- not merely *a* fixed point.  Target-side climb toward ψ₀(Ω_ω) (BH
-- order-type fidelity, open problem D-2026-06-14).  Builds on
-- `VeblenBinary` (the engine + Γ₀) and `VeblenBinaryNormal`
-- (`φ-mono₂` / `commonStep-mono`).  2026-06-20.
--
-- ## What this slice adds
--
-- `VeblenBinary` proved `nextFix g x` is a fixed point of `g`
-- (`nextFix-fixed-{≤,≥}`) lying strictly above `x` (`nextFix-above`).
-- The missing half of the engine's correctness is MINIMALITY:
--
--   * `nextFix-least` — for monotone `g`, if `x <′ z` and `g z ≤′ z`
--     (z is a pre-fixed point of g strictly above x) then
--     `nextFix g x ≤′ z`.  So `nextFix g x` is the LEAST pre-fixed
--     point of g strictly above x.  Proof: every approximant of the
--     iteration tower `g-tower g (osuc x)` is `≤′ z` — the base by
--     `x <′ z`, each successor by monotonicity into the pre-fixed
--     point `g z ≤′ z`; the supremum is then `≤′ z` definitionally
--     (`olim T ≤′ z` unfolds to `∀ n → T n ≤′ z`).
--
-- This is exactly the tool the reverse Γ₀ fixed-point direction (and
-- "Γ₀ is the LEAST diagonal fixed point") needs, and which
-- `VeblenBinaryMono` flagged as the open "common-fixed-point-from-above"
-- piece.  As an immediate payoff:
--
--   * `Γ₀-fixed-from-closure` — REDUCES the open reverse direction
--     `φ_Γ₀(0) ≤′ Γ₀` to a single closure obligation
--     `commonStep (n ↦ φ_{Γ-tower n}) Γ₀ ≤′ Γ₀` (Γ₀ is closed under
--     every diagonal-approximant level applied to Γ₀ itself).  Because
--     `φ Γ₀ oz` is, definitionally, `nextFix (commonStep …) oz`, the
--     reduction is just `nextFix-least` at `x = oz`, `z = Γ₀`
--     (`Γ₀-pos` supplies `oz <′ Γ₀`).
--
-- ## Honest scope (still a LONG climb — do not overclaim)
--
-- `nextFix-least` is a real, unconditional theorem.  `Γ₀-fixed-from-
-- closure` is a CONDITIONAL: it does NOT prove `φ_Γ₀(0) ≤′ Γ₀`; it
-- proves it FOLLOWS from the closure `commonStep F Γ₀ ≤′ Γ₀`, which
-- needs general first-argument monotonicity and REMAINS OPEN (the next
-- slice).  Combined with `VeblenBinaryMono.Γ₀-prefixed` (the `≤′`
-- direction), discharging that one closure obligation would give the
-- full bi-`≤′` fixed point `Γ₀ ≃ φ_Γ₀(0)`.  ψ₀(Ω_ω) sits far above Γ₀
-- behind the ordinal-collapsing layer; order-type fidelity REMAINS OPEN
-- (D-2026-06-14).  No postulate is closed.

module Ordinal.Brouwer.VeblenBinaryLeast where

open import Data.Nat.Base using (ℕ; zero; suc)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13 using (_≤′_; _<′_; ≤′-trans)
open import Ordinal.Brouwer.VeblenBinary
  using (g-tower; nextFix; deriv; commonStep; φ; Γ-tower; Γ₀; Γ₀-pos)
open import Ordinal.Brouwer.VeblenBinaryNormal using (φ-mono₂; commonStep-mono)

----------------------------------------------------------------------
-- Minimality of the generic fixed-point engine.
--
-- `nextFix g x = olim (g-tower g (osuc x))`, so `nextFix g x ≤′ z`
-- unfolds (by the `olim f ≤′ β = ∀ n → f n ≤′ β` clause of `_≤′_`) to
-- "every tower approximant is `≤′ z`".  We prove that by induction on
-- the tower index against a pre-fixed point `z` strictly above `x`.
----------------------------------------------------------------------

nextFix-least :
  (g : Ord → Ord) (g-mono : ∀ {a b} → a ≤′ b → g a ≤′ g b)
  {x z : Ord} → x <′ z → g z ≤′ z → nextFix g x ≤′ z
nextFix-least g g-mono {x} {z} x<z gz≤z = tower≤
  where
    tower≤ : ∀ n → g-tower g (osuc x) n ≤′ z
    tower≤ zero    = x<z
    tower≤ (suc n) =
      ≤′-trans {g (g-tower g (osuc x) n)} {g z} {z}
        (g-mono {g-tower g (osuc x) n} {z} (tower≤ n))
        gz≤z

----------------------------------------------------------------------
-- Payoff: the reverse Γ₀ fixed-point direction reduces to one closure.
--
-- `φ Γ₀ oz` is definitionally `nextFix (commonStep F) oz` where
-- `F n = φ (Γ-tower n)` (φ-olim recurrence + `deriv g oz = nextFix g oz`),
-- so `nextFix-least` at `x = oz`, `z = Γ₀` turns the open
-- `φ_Γ₀(0) ≤′ Γ₀` into the single closure obligation below.
----------------------------------------------------------------------

Γ₀-fixed-from-closure :
  commonStep (λ n → φ (Γ-tower n)) Γ₀ ≤′ Γ₀ →
  φ Γ₀ oz ≤′ Γ₀
Γ₀-fixed-from-closure closure =
  nextFix-least (commonStep F)
    (commonStep-mono F (λ n {x} {y} → φ-mono₂ (Γ-tower n) {x} {y}))
    {oz} {Γ₀} Γ₀-pos closure
  where
    F : ℕ → Ord → Ord
    F n = φ (Γ-tower n)
