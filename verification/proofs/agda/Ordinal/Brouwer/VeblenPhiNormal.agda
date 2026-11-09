{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Veblen φ-hierarchy over Brouwer ordinals — RUNG 3 (slice 3): φ₁ is a
-- NORMAL FUNCTION, and `next-ε β` is the LEAST ε-number above β.  Target-
-- side climb toward ψ₀(Ω_ω) (BH order-type fidelity, open problem
-- D-2026-06-14).  Builds directly on `VeblenPhi` (φ₁ / next-ε defined and
-- proved ε-valued) and `OrdinalExp` (ω^^).  2026-06-19.
--
-- ## What this slice adds
--
-- The previous slice (`VeblenPhi`) proved that every value of φ₁ IS an
-- ε-number (`φ₁-ε-number`) and that `next-ε β` is AN ε-number strictly
-- above β.  This slice upgrades that to the two defining properties of an
-- ε-number ENUMERATION:
--
--   * `next-ε-least` — `next-ε β` is the LEAST ω^^-closed ordinal strictly
--     above β.  This is what makes `next-ε` the genuine "next ε-number"
--     operator (not merely *an* ε-number above β).  Definitional, because
--     `olim f ≤′ γ` reduces to `∀ n → f n ≤′ γ` (olim is the least upper
--     bound), so the proof is induction on the ω^^-tower index using
--     ω^^-monotonicity + the ω^^-closure hypothesis on γ.
--   * `φ₁` is a NORMAL FUNCTION:
--       - `φ₁-mono`        — monotone               (α ≤′ β → φ₁ α ≤′ φ₁ β)
--       - `φ₁-strict-mono` — strictly monotone      (α <′ β → φ₁ α <′ φ₁ β)
--       - `φ₁-continuous`  — continuous at limits    (definitional, `refl`)
--     A normal function is precisely a strictly-monotone, continuous
--     ordinal function; φ₁ is now mechanically one.
--
-- The one prerequisite the previous slices left open is `ω^^-mono-≤′`
-- (monotonicity of ω-exponentiation), proved here by structural recursion
-- on the `_≤′_` shape; it is a pure ω^^ fact and a natural candidate to
-- migrate into `OrdinalExp` when the binary Veblen rung needs it.
--
-- ## Honest scope (still rung 3 of a LONG climb — do not overclaim)
--
-- φ₁ being a normal function is the standard precondition for taking its
-- fixed points (the next Veblen level) and ultimately the binary φ_α and
-- its diagonal → Γ₀.  It does NOT reach Γ₀, and ψ₀(Ω_ω) sits far above
-- even Γ₀ and additionally needs the ordinal-collapsing layer.  Order-type
-- fidelity (ψ₀(Ω_ω)) REMAINS OPEN (D-2026-06-14); this slice neither
-- reaches Γ₀ nor plugs `Fidelity.carrier-height`.  bi-`≤′` (not `≡`) is used for
-- the fixed-point facts because Brouwer `olim`s of different ℕ-indexings of
-- one supremum are not definitionally equal; the monotonicity results are
-- single-`≤′` / single-`<′` and exact.

module Ordinal.Brouwer.VeblenPhiNormal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13
  using (_≤′_; _<′_; ≤′-refl; ≤′-trans; ≤′-lim; ≤′-self-osuc)
open import Ordinal.Brouwer.OmegaPow using (_·ℕ_; ·ℕ-mono-≤-left)
open import Ordinal.Brouwer.OrdinalExp using (ω^^_; ε₀; ω^^-pos)
open import Ordinal.Brouwer.VeblenPhi
  using (tower-from; next-ε; φ₁; ω^^-next-ε-≤; β<next-ε)

----------------------------------------------------------------------
-- ω-exponentiation is monotone (the one missing prerequisite).
--
-- `α ≤′ β → ω^^ α ≤′ ω^^ β`, by structural recursion on the `_≤′_` shape
-- of (α, β) — the same descent pattern as `Phase13.≤′-trans`.  Uses only
-- ω^^-positivity (the `oz` base), `·ℕ`-left-monotonicity (the
-- successor/successor case, where `ω^^ (osuc α) = olim (n ↦ ω^^ α ·ℕ n)`),
-- and the olim least-upper-bound `≤′-lim`.
----------------------------------------------------------------------

ω^^-mono-≤′ : ∀ {α β} → α ≤′ β → ω^^ α ≤′ ω^^ β
ω^^-mono-≤′ {oz}     {β}      _       = ω^^-pos β
ω^^-mono-≤′ {osuc α} {oz}     p       = ⊥-elim p
ω^^-mono-≤′ {osuc α} {osuc β} p       =
  λ n → ≤′-lim {(ω^^ α) ·ℕ n} (λ m → (ω^^ β) ·ℕ m) n
          (·ℕ-mono-≤-left {ω^^ α} {ω^^ β} n (ω^^-mono-≤′ {α} {β} p))
ω^^-mono-≤′ {osuc α} {olim f} (n , q) =
  ≤′-lim {ω^^ (osuc α)} (λ k → ω^^ (f k)) n (ω^^-mono-≤′ {osuc α} {f n} q)
ω^^-mono-≤′ {olim g} {β}      p       =
  λ n → ω^^-mono-≤′ {g n} {β} (p n)

----------------------------------------------------------------------
-- `next-ε β` is the LEAST ω^^-closed ordinal strictly above β.
--
-- For any γ with `osuc β ≤′ γ` (β strictly below γ) and `ω^^ γ ≤′ γ`
-- (γ is closed under ω-exponentiation — the direction of the ε-number
-- property we need), `next-ε β ≤′ γ`.  `next-ε β = olim (tower-from
-- (osuc β))`, and `olim … ≤′ γ` is definitionally "every tower approximant
-- is ≤′ γ", proved by induction on the tower index n:
--   * n = 0  : `tower-from (osuc β) 0 = osuc β ≤′ γ`           (hypothesis)
--   * n+1    : `ω^^ (tower-from … n) ≤′ ω^^ γ ≤′ γ`            (ω^^-mono + closure)
----------------------------------------------------------------------

next-ε-least : ∀ {β γ} → osuc β ≤′ γ → ω^^ γ ≤′ γ → next-ε β ≤′ γ
next-ε-least {β} {γ} β<γ ω^^γ≤γ = go
  where
  go : ∀ n → tower-from (osuc β) n ≤′ γ
  go zero    = β<γ
  go (suc m) =
    ≤′-trans {ω^^ (tower-from (osuc β) m)} {ω^^ γ} {γ}
      (ω^^-mono-≤′ {tower-from (osuc β) m} {γ} (go m)) ω^^γ≤γ

-- Monotonicity of `next-ε`: a larger base gives a larger next ε-number.
-- By `next-ε-least` with γ := next-ε β (which is ω^^-closed by
-- `ω^^-next-ε-≤`), since `osuc α ≤′ osuc β ≤′ next-ε β`.
next-ε-mono : ∀ {α β} → α ≤′ β → next-ε α ≤′ next-ε β
next-ε-mono {α} {β} p =
  next-ε-least {α} {next-ε β}
    (≤′-trans {osuc α} {osuc β} {next-ε β} p (β<next-ε β))
    (ω^^-next-ε-≤ β)

----------------------------------------------------------------------
-- ε₀ is the least value of φ₁ (φ₁ oz), hence ≤′ every φ₁ value.
-- The `oz` base case of monotonicity; recursion on β alone.
----------------------------------------------------------------------

ε₀-least : ∀ β → ε₀ ≤′ φ₁ β
ε₀-least oz       = ≤′-refl {ε₀}
ε₀-least (osuc β) =
  ≤′-trans {ε₀} {φ₁ β} {next-ε (φ₁ β)}
    (ε₀-least β)
    (≤′-trans {φ₁ β} {osuc (φ₁ β)} {next-ε (φ₁ β)}
      (≤′-self-osuc (φ₁ β)) (β<next-ε (φ₁ β)))
ε₀-least (olim f) = ≤′-lim {ε₀} (λ n → φ₁ (f n)) 0 (ε₀-least (f 0))

----------------------------------------------------------------------
-- φ₁ is a NORMAL FUNCTION.
----------------------------------------------------------------------

-- Monotone.  Structural recursion on the `_≤′_` shape of (α, β):
--   * oz base reduces to `ε₀-least`;
--   * successor/successor is `next-ε-mono` of the inductive step;
--   * the two olim cases thread through `≤′-lim` / the pointwise olim rule.
φ₁-mono : ∀ {α β} → α ≤′ β → φ₁ α ≤′ φ₁ β
φ₁-mono {oz}     {β}      _       = ε₀-least β
φ₁-mono {osuc α} {oz}     p       = ⊥-elim p
φ₁-mono {osuc α} {osuc β} p       = next-ε-mono {φ₁ α} {φ₁ β} (φ₁-mono {α} {β} p)
φ₁-mono {osuc α} {olim f} (n , q) =
  ≤′-lim {φ₁ (osuc α)} (λ k → φ₁ (f k)) n (φ₁-mono {osuc α} {f n} q)
φ₁-mono {olim g} {β}      p       = λ n → φ₁-mono {g n} {β} (p n)

-- Strictly increasing at successors: φ₁ α <′ φ₁ (osuc α).  Immediate,
-- since `φ₁ (osuc α) = next-ε (φ₁ α)` and `β<next-ε` places `φ₁ α` strictly
-- below `next-ε (φ₁ α)`.
φ₁-lt-succ : ∀ α → φ₁ α <′ φ₁ (osuc α)
φ₁-lt-succ α = β<next-ε (φ₁ α)

-- Strictly monotone.  `α <′ β` is `osuc α ≤′ β`; chain the successor jump
-- `φ₁ α <′ φ₁ (osuc α)` with `φ₁ (osuc α) ≤′ φ₁ β` (monotonicity).
φ₁-strict-mono : ∀ {α β} → α <′ β → φ₁ α <′ φ₁ β
φ₁-strict-mono {α} {β} α<β =
  ≤′-trans {osuc (φ₁ α)} {φ₁ (osuc α)} {φ₁ β}
    (φ₁-lt-succ α) (φ₁-mono {osuc α} {β} α<β)

-- Continuous at limits.  φ₁ commutes with `olim` definitionally
-- (the `olim` clause of φ₁), so continuity is `refl` — exactly the
-- supremum-preservation a normal function requires.
φ₁-continuous : ∀ f → φ₁ (olim f) ≡ olim (λ n → φ₁ (f n))
φ₁-continuous f = refl
