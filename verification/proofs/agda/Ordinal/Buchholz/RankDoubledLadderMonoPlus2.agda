{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Doubled-ladder rank monotonicity — the last two bplus-on-left
-- primitives `<ᵇ-+ψ`, `<ᵇ-+1` (2026-06-14).
--
-- ## Why this exists
--
-- With `<ᵇ-+Ω` closed (`RankDoubledLadderAddPrincipal`), the two
-- remaining bplus-on-left constructors of the core `_<ᵇ_` are:
--
--   * `<ᵇ-+ψ : x <ᵇ bpsi ν α → bplus x y <ᵇ bpsi ν α`
--   * `<ᵇ-+1 : x₁ <ᵇ y₁ → bplus x₁ x₂ <ᵇ bplus y₁ y₂`
--
-- Both ship as relation-agnostic `rank2`-mono primitives — the same
-- discipline as the rest of the family.  The genuinely-hard content
-- (discharging the premise bounds from the WfCNF tail order `y ≤ᵇ x`
-- and the sub-derivations) lives in the umbrella that consumes these;
-- the primitives themselves are pure `⊕`-arithmetic:
--
--   * `<ᵇ-+ψ` — the ψ-block leading power `ω-rank-pow (double ν)` is
--     additive principal (`RankPow.additive-principal-ω-rank-pow`), so
--     if BOTH source summands rank below it, their sum does too, and
--     the target ψ-rank only ADDS its argument on the right.
--   * `<ᵇ-+1` — if the WHOLE source sum ranks below the target's HEAD
--     `rank2 y₁`, then it ranks below the target sum (the target's tail
--     only adds).
--
-- ## Completion
--
-- With these two, ALL 12 core `_<ᵇ_` constructors have a `rank2`-mono
-- primitive.  The follow-on is the umbrella
-- `rank2-mono : WfAdm x → WfAdm y → x <ᵇ y → rank2 x <′ rank2 y`
-- (structural recursion that discharges each primitive's premises,
-- needing a `rank2-mono-≤` tail-bound companion for `y ≤ᵇ x`) and the
-- `wf-<′`-transport headline `wf-<ᵇ`.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `rank2-mono-+ψ`
--   * `rank2-mono-+1`

module Ordinal.Buchholz.RankDoubledLadderMonoPlus2 where

open import Ordinal.Brouwer.Phase13       using (_<′_; ⊕-left-≤-sum)
open import Ordinal.Brouwer.Arithmetic    using (_⊕_)
open import Ordinal.Buchholz.Syntax       using (BT; bpsi; bplus)
open import Ordinal.Buchholz.RankPow       using (ω-rank-pow; additive-principal-ω-rank-pow)
open import Ordinal.Buchholz.RankDoubledLadder using (rank2; double)
open import Ordinal.Buchholz.RankDoubledLadderMono using (<′-≤′-trans)

----------------------------------------------------------------------
-- `<ᵇ-+ψ` — bplus source against a ψ target
----------------------------------------------------------------------

-- `<ᵇ-+ψ : x <ᵇ bpsi ν α → bplus x y <ᵇ bpsi ν α`.  The ψ-block
-- leading power `ω-rank-pow (double ν)` is additive principal, so
-- both source summands ranking below it makes the sum rank below it;
-- the target ψ-rank `ω-rank-pow (double ν) ⊕ rank2 α` then only adds.
-- Premises (supplied by the umbrella): the left bound is the IH on
-- `x <ᵇ bpsi ν α`, the right is the tail bound from `y ≤ᵇ x`.
rank2-mono-+ψ : ∀ {x y ν α}
  → rank2 x <′ ω-rank-pow (double ν)
  → rank2 y <′ ω-rank-pow (double ν)
  → rank2 (bplus x y) <′ rank2 (bpsi ν α)
rank2-mono-+ψ {x} {y} {ν} {α} px py =
  <′-≤′-trans {rank2 x ⊕ rank2 y} {ω-rank-pow (double ν)}
              {ω-rank-pow (double ν) ⊕ rank2 α}
    (additive-principal-ω-rank-pow {double ν} px py)
    (⊕-left-≤-sum {ω-rank-pow (double ν)} (rank2 α))

----------------------------------------------------------------------
-- `<ᵇ-+1` — joint bplus
----------------------------------------------------------------------

-- `<ᵇ-+1 : x₁ <ᵇ y₁ → bplus x₁ x₂ <ᵇ bplus y₁ y₂`.  If the WHOLE
-- source sum ranks below the target's HEAD `rank2 y₁`, it ranks below
-- the target sum (the target tail `rank2 y₂` only adds on the right).
-- The premise — source sum below target head — is what the umbrella
-- derives from `x₁ <ᵇ y₁` plus the tail order `x₂ ≤ᵇ x₁`; this is the
-- joint-bplus discharge the doubled ladder was ultimately built for.
rank2-mono-+1 : ∀ {x₁ x₂ y₁ y₂}
  → rank2 (bplus x₁ x₂) <′ rank2 y₁
  → rank2 (bplus x₁ x₂) <′ rank2 (bplus y₁ y₂)
rank2-mono-+1 {x₁} {x₂} {y₁} {y₂} p =
  <′-≤′-trans {rank2 x₁ ⊕ rank2 x₂} {rank2 y₁} {rank2 y₁ ⊕ rank2 y₂}
    p
    (⊕-left-≤-sum {rank2 y₁} (rank2 y₂))
