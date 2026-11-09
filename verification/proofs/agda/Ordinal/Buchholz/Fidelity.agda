{-# OPTIONS --without-K #-}

-- hypatia: allow code_safety/agda_postulate -- order-type fidelity for the Buchholz notation (D-2026-06-14) is open mathematics; the TWO named postulates below (carrier-height, denotation) are the explicit, documented trust boundary. This module is OUTSIDE the --safe kernel cone by design, is NOT imported by All.agda/Smoke.agda, and asserts NOTHING that the --safe core depends on. See Fidelity-OPEN-postulates.adoc.

-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Order-type SPECIFICATION for the sound Buchholz carrier
-- (open problem D-2026-06-14).  Restated 2026-11-09.
--
-- ## Why it was restated
--
-- The 2026-06-15 version postulated, for EVERY candidate height, a
-- denotation whose image was cofinal in all of `Ord` together with an
-- upper bound at that height.  Instantiating `cofinal` at the height
-- contradicted `ordinal-upper-bound`, so ⊥ was derivable inside
-- `AtHeight`; and because the postulates were universally quantified
-- over the height, a height such as `oz` gave a second contradiction.
-- It also stated the claim over `WfBT`, although `_<ᵇ²_` only relates
-- `WfAdm` terms on its ψ-sources, and it pinned the term `BH` to the
-- height, although `BH` is not `WfAdm`.
--
-- ## What this module states now
--
-- The order type of the SOUND carrier: well-formed admissible terms
-- (`WfAdm`) under `_<ᵇ²_`.  A denotation `⟦_⟧` into the real Brouwer
-- order (`bh-notation-from`, --safe, in BHTarget.agda) that
--
--   * preserves `_<ᵇ²_`,
--   * reflects it, up to transitive closure (no transitivity lemma for
--     `_<ᵇ²_` exists, and `_<′_` is transitive, so reflecting into
--     `_<ᵇ²_` itself could force a transitivity that may be false),
--   * is strictly bounded by the height, and
--   * is cofinal BELOW the height in the non-strict sense: every `o`
--     below the height is not above some denotation, `¬ (⟦ t ⟧ <𝒪 o)`.
--     Strict cofinality (`o <𝒪 ⟦ t ⟧`) is unsatisfiable: the carrier has
--     a maximum (`bOmega ω` has no outgoing `_<ᵇ²_` edge), and strict
--     cofinality at its own denotation plus `reflect` would demand an edge
--     out of it.  (Corrected 2026-11-09, review on ordinal-notation#6.)
--
-- The height is a single postulated `Ord`, not a parameter, so the
-- postulates assert ONE existence claim instead of one per candidate.
--
-- ## What this module is NOT
--
--   * NOT the ψ₀(Ω_ω) claim.  `_<ᵇ²_` has no same-index ψ comparison,
--     so the carrier omits the ψ₀ fragment of the Buchholz order.
--     Whatever its height is, identifying it with ψ₀(Ω_ω) is a further
--     OPEN step that needs a carrier with that fragment.
--   * NOT `rank2`.  `rank2` is the height-collapsing termination measure:
--     monotone, but neither order-reflecting nor cofinal.
--   * NOT in the --safe cone (pragma `--without-K` only, because of the
--     postulates).  Not imported by `All.agda` / `Smoke.agda`.
--
-- ## Trust boundary (grep `postulate`)
--
--   * `carrier-height` — the height of the sound carrier, in `Ord`.
--   * `denotation`     — the bounded, cofinal, preserving and reflecting
--                        map into the Brouwer order below that height.
--
-- See Fidelity-OPEN-postulates.adoc for what discharges each.

module Ordinal.Buchholz.Fidelity where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)

open import Ordinal.OmegaMarkers using (OmegaIndex; fin; ω; _≤Ω_; fin≤ω; ω≤ω)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.WellFormedAdmissible using (WfAdm)
open import Ordinal.Buchholz.RankDoubledLadderUmbrella using (_<ᵇ²_)

open import Ordinal.Brouwer using (Ord)
open import Ordinal.Buchholz.BHTarget using (BHNotation; bh-notation-from)

----------------------------------------------------------------------
-- 1. The specification of a faithful denotation below a height
----------------------------------------------------------------------

record DenotesBelow (N : BHNotation) : Set where
  open BHNotation N
  field
    ⟦_⟧      : BT → 𝒪
    preserve : ∀ {s t} → WfAdm s → WfAdm t → s <ᵇ² t → ⟦ s ⟧ <𝒪 ⟦ t ⟧
    reflect  : ∀ {s t} → WfAdm s → WfAdm t → ⟦ s ⟧ <𝒪 ⟦ t ⟧ →
               TransClosure _<ᵇ²_ s t
    bounded  : ∀ {t} → WfAdm t → ⟦ t ⟧ <𝒪 bh-height
    cofinal  : ∀ {o} → o <𝒪 bh-height →
               Σ BT (λ t → WfAdm t × ¬ (⟦ t ⟧ <𝒪 o))

----------------------------------------------------------------------
-- 2. Proved for real: the grammar-level marker bound
----------------------------------------------------------------------

-- Every Ω-marker occurring in a Buchholz term is ≤Ω ω.  This follows
-- from the constructor shapes (OmegaIndex is exactly `fin n | ω`).  It
-- is the structural precondition for any height bound, not the bound.

AllMarkers≤ω : BT → Set
AllMarkers≤ω bzero       = ⊤
AllMarkers≤ω (bOmega ν)  = ν ≤Ω ω
AllMarkers≤ω (bplus x y) = AllMarkers≤ω x × AllMarkers≤ω y
AllMarkers≤ω (bpsi ν α)  = (ν ≤Ω ω) × AllMarkers≤ω α

marker-≤ω : (ν : OmegaIndex) → ν ≤Ω ω
marker-≤ω (fin n) = fin≤ω
marker-≤ω ω       = ω≤ω

markers-≤ω : (t : BT) → AllMarkers≤ω t
markers-≤ω bzero       = tt
markers-≤ω (bOmega ν)  = marker-≤ω ν
markers-≤ω (bplus x y) = markers-≤ω x , markers-≤ω y
markers-≤ω (bpsi ν α)  = marker-≤ω ν , markers-≤ω α

----------------------------------------------------------------------
-- 3. The open claim
----------------------------------------------------------------------

-- TRUST BOUNDARY #1 (of 2).
-- AXIOM: carrier-height — assumed; OPEN proof-debt (D-2026-06-14); see Fidelity-OPEN-postulates.adoc. NOT a permanently accepted axiom.
postulate
  carrier-height : Ord

carrier-notation : BHNotation
carrier-notation = bh-notation-from carrier-height

-- TRUST BOUNDARY #2 (of 2).
-- AXIOM: denotation — assumed; OPEN proof-debt (D-2026-06-14); see Fidelity-OPEN-postulates.adoc. NOT a permanently accepted axiom.
postulate
  denotation : DenotesBelow carrier-notation

-- The order-type claim for the sound carrier, assembled.  It is only as
-- strong as the two postulates.
OrderTypeOfSoundCarrier : Set
OrderTypeOfSoundCarrier = DenotesBelow carrier-notation

order-type : OrderTypeOfSoundCarrier
order-type = denotation
