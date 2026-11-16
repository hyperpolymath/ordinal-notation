{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Doubled-ladder rank monotonicity — bzero-source + plus-source slice
-- (2026-06-14).
--
-- ## Why this exists
--
-- `RankDoubledLadderMono` discharged the four ATOMIC-vs-atomic
-- `_<ᵇ_` constructors (`<ᵇ-ΩΩ/Ωψ/ψΩ/ψΩ≤`).  This slice adds the
-- per-constructor `rank2`-mono primitives for the constructors whose
-- monotonicity is pure `⊕`-weakening / positivity — no admissibility
-- and no additive-principality needed:
--
--   * bzero-source (`<ᵇ-0-Ω/0-ψ/0-+`) — positivity of the target rank;
--   * plus-source with an ATOMIC left witness (`<ᵇ-Ω+`, `<ᵇ-ψ+`) —
--     the constructor recurses on a sub-derivation `bOmega μ <ᵇ x` /
--     `bpsi ν α <ᵇ x`; given the recursive result `rank2 atom <′
--     rank2 x` (the IH), the bplus target only ADDS on the right, so
--     `⊕-left-≤-sum` finishes.
--
-- These mirror the `<ᵇ-0-*` / `<ᵇ-Ω+` / `<ᵇ-ψ+` primitives RankPow
-- shipped for the single ladder: each is stated relation-agnostically
-- (the recursive case takes the IH as its premise), so a `_<ᵇ_`
-- consumer pattern-matches on its own constructor, recurses, and
-- applies the matching primitive.
--
-- ## Honest scope
--
-- NOT in this slice (the genuinely-recursive bplus-ON-LEFT cases,
-- deferred to the final umbrella slice): `<ᵇ-+Ω`, `<ᵇ-+ψ`, `<ᵇ-+1`.
-- Those need additive-principality of the `rank2` TARGET
-- (`additive-principal-ω-rank-pow-succ` for `<ᵇ-+Ω`; the joint-bplus
-- tail bound `y ≤ᵇ x` for `<ᵇ-+1`) — the same shape that made the
-- single-ladder `<ᵇ-+1` Gate 1's last residual.  With those three the
-- full `rank2-mono : WfAdm x → WfAdm y → x <ᵇ y → rank2 x <′ rank2 y`
-- umbrella + the `wf-<′`-transport headline `wf-<ᵇ` close.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `rank2-pos-bOmega`  (`<ᵇ-0-Ω`)
--   * `rank2-pos-bpsi`    (`<ᵇ-0-ψ`)
--   * `rank2-mono-0-+`    (`<ᵇ-0-+`)
--   * `rank2-mono-Ω+`     (`<ᵇ-Ω+`)
--   * `rank2-mono-ψ+`     (`<ᵇ-ψ+`)

module Ordinal.Buchholz.RankDoubledLadderMonoPlus where

open import Ordinal.Brouwer               using (Ord; oz)
open import Ordinal.Brouwer.Phase13       using (_<′_; ⊕-left-≤-sum)
open import Ordinal.Brouwer.Arithmetic    using (_⊕_)
open import Ordinal.OmegaMarkers          using (OmegaIndex)
open import Ordinal.Buchholz.Syntax       using (BT; bOmega; bpsi; bplus)
open import Ordinal.Buchholz.RankPow       using
  ( ω-rank-pow
  ; ω-rank-pow-succ
  ; ω-rank-pow-pos
  ; ω-rank-pow-<-succ
  )
open import Ordinal.Buchholz.RankDoubledLadder using (rank2; double)
open import Ordinal.Buchholz.RankDoubledLadderMono using (<′-trans; <′-≤′-trans)

----------------------------------------------------------------------
-- bzero-source positivity (`<ᵇ-0-Ω`, `<ᵇ-0-ψ`)
----------------------------------------------------------------------

-- `<ᵇ-0-Ω` — `oz <′ rank2 (bOmega μ)`.  The Ω-block rank is `oz <′
-- ω-rank-pow (double μ) <′ ω-rank-pow-succ (double μ)`.
rank2-pos-bOmega : ∀ μ → oz <′ rank2 (bOmega μ)
rank2-pos-bOmega μ =
  <′-trans {oz} {ω-rank-pow (double μ)} {ω-rank-pow-succ (double μ)}
    (ω-rank-pow-pos (double μ))
    (ω-rank-pow-<-succ (double μ))

-- `<ᵇ-0-ψ` — `oz <′ rank2 (bpsi ν α)`.  The ψ-rank's leading block is
-- positive and the ψ-argument only adds (`⊕-left-≤-sum`).
rank2-pos-bpsi : ∀ ν α → oz <′ rank2 (bpsi ν α)
rank2-pos-bpsi ν α =
  <′-≤′-trans {oz} {ω-rank-pow (double ν)} {ω-rank-pow (double ν) ⊕ rank2 α}
    (ω-rank-pow-pos (double ν))
    (⊕-left-≤-sum {ω-rank-pow (double ν)} (rank2 α))

----------------------------------------------------------------------
-- plus-source primitives (`<ᵇ-0-+`, `<ᵇ-Ω+`, `<ᵇ-ψ+`)
----------------------------------------------------------------------

-- `<ᵇ-0-+` — `oz <′ rank2 (bplus x y)` from left-positivity.  The
-- consumer supplies `oz <′ rank2 x` (from well-formedness of the
-- bplus head); the right summand only adds.
rank2-mono-0-+ : ∀ {x y}
  → oz <′ rank2 x
  → oz <′ rank2 (bplus x y)
rank2-mono-0-+ {x} {y} p =
  <′-≤′-trans {oz} {rank2 x} {rank2 x ⊕ rank2 y}
    p
    (⊕-left-≤-sum {rank2 x} (rank2 y))

-- `<ᵇ-Ω+` — `bOmega μ <ᵇ x → bOmega μ <ᵇ bplus x y`.  Premise is the
-- recursive result `rank2 (bOmega μ) <′ rank2 x`; the bplus target
-- adds on the right.
rank2-mono-Ω+ : ∀ {μ x y}
  → rank2 (bOmega μ) <′ rank2 x
  → rank2 (bOmega μ) <′ rank2 (bplus x y)
rank2-mono-Ω+ {μ} {x} {y} p =
  <′-≤′-trans {rank2 (bOmega μ)} {rank2 x} {rank2 x ⊕ rank2 y}
    p
    (⊕-left-≤-sum {rank2 x} (rank2 y))

-- `<ᵇ-ψ+` — `bpsi ν α <ᵇ x → bpsi ν α <ᵇ bplus x y`.  Same shape as
-- `<ᵇ-Ω+`, premise = the recursive result `rank2 (bpsi ν α) <′
-- rank2 x`.
rank2-mono-ψ+ : ∀ {ν α x y}
  → rank2 (bpsi ν α) <′ rank2 x
  → rank2 (bpsi ν α) <′ rank2 (bplus x y)
rank2-mono-ψ+ {ν} {α} {x} {y} p =
  <′-≤′-trans {rank2 (bpsi ν α)} {rank2 x} {rank2 x ⊕ rank2 y}
    p
    (⊕-left-≤-sum {rank2 x} (rank2 y))
