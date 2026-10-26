{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Aggregator for the whole verified ordinal-notation development: every module
-- below typechecks under --safe --without-K with zero postulates.
--
-- NOT included, on purpose: Ordinal/Buchholz/Fidelity.agda. It carries the two
-- quarantined postulates (`denotation`, `ordinal-upper-bound`), so it cannot be
-- --safe. See Fidelity-OPEN-postulates.adoc.

module All where

open import Ordinal.Base
open import Ordinal.Closure
open import Ordinal.CNF
open import Ordinal.PsiSimple
open import Ordinal.OmegaMarkers
open import Ordinal.Brouwer
open import Ordinal.Brouwer.Arithmetic
open import Ordinal.Brouwer.Phase13
open import Ordinal.Brouwer.OmegaPow
open import Ordinal.Brouwer.OrdinalExp
open import Ordinal.Brouwer.VeblenPhi
open import Ordinal.Brouwer.VeblenPhiNormal -- φ₁ a normal function; next-ε β LEAST ε-number above β
open import Ordinal.Brouwer.VeblenBinary    -- binary Veblen φ_α(β) + the diagonal Γ₀
open import Ordinal.Brouwer.VeblenBinaryNormal -- every φ_α a normal function; φ_{α+1} enumerates fixed points of φ_α
open import Ordinal.Brouwer.VeblenBinaryMono -- first-arg monotonicity; Γ₀ ≤′ φ_Γ₀(0) (diagonal pre-fixed point)
open import Ordinal.Brouwer.VeblenBinaryLeast -- nextFix is the LEAST pre-fixed point; reverse-Γ₀ reduced to one closure
open import Ordinal.Brouwer.VeblenBinaryMonoG -- the engine is monotone in its iterated function (deriv/nextFix mono in g)
open import Ordinal.Brouwer.StrictLeftMonoRefuted
open import Ordinal.Brouwer.AdditivePrincipalGenericRefuted
open import Ordinal.Buchholz.Syntax
open import Ordinal.Buchholz.Closure
open import Ordinal.Buchholz.Order
open import Ordinal.Buchholz.OrderExtended
open import Ordinal.Buchholz.OrderExtendedBudget
open import Ordinal.Buchholz.Psi
open import Ordinal.Buchholz.Examples
open import Ordinal.Buchholz.WellFormed
open import Ordinal.Buchholz.WellFormedCNF
open import Ordinal.Buchholz.WellFormedAdmissible
open import Ordinal.Buchholz.WellFounded
open import Ordinal.Buchholz.OrderRestricted
open import Ordinal.Buchholz.VeblenInterface
open import Ordinal.Buchholz.VeblenIdentityModel
open import Ordinal.Buchholz.VeblenMeasureTarget
open import Ordinal.Buchholz.VeblenProjectionMeasure
open import Ordinal.Buchholz.VeblenComparisonTarget
open import Ordinal.Buchholz.VeblenComparisonModel
open import Ordinal.Buchholz.ExtendedOrder
open import Ordinal.Buchholz.OrderExtendedDirect
open import Ordinal.Buchholz.LiftedExtendedOrder
open import Ordinal.Buchholz.IteratedExtendedOrder
open import Ordinal.Buchholz.RankBrouwer
open import Ordinal.Buchholz.RankPartial
open import Ordinal.Buchholz.RankPow
open import Ordinal.Buchholz.RankAdm
open import Ordinal.Buchholz.RankLex
open import Ordinal.Buchholz.RankLexSlice3
open import Ordinal.Buchholz.RankLexJointBplus
open import Ordinal.Buchholz.HeadOmega
open import Ordinal.Buchholz.HeadOmegaInversion
open import Ordinal.Buchholz.RankPowDomination
open import Ordinal.Buchholz.RankPowSlice3
open import Ordinal.Buchholz.RankPowSlice3Headline
open import Ordinal.Buchholz.RankPowMonoRefuted
open import Ordinal.Buchholz.RankDoubledLadder
open import Ordinal.Buchholz.RankDoubledLadderMono
open import Ordinal.Buchholz.RankDoubledLadderMonoPlus
open import Ordinal.Buchholz.RankDoubledLadderAddPrincipal
open import Ordinal.Buchholz.RankDoubledLadderMonoPlus2
open import Ordinal.Buchholz.RankDoubledLadderUmbrella
open import Ordinal.Buchholz.BHTarget
open import Ordinal.Buchholz.RankMonoUmbrella
open import Ordinal.Buchholz.RankMonoUmbrellaSlice3
open import Ordinal.Buchholz.RankMonoUmbrellaSlice4
open import Ordinal.Buchholz.RankMonoSameLeft
open import Ordinal.Buchholz.RankMonoUnion
open import Ordinal.Buchholz.RankMonoUnionWF
open import Ordinal.Buchholz.RankMonoUnionWfCNF
open import Ordinal.Buchholz.RecursiveSurfaceOrder
open import Ordinal.Buchholz.RecursiveSurfaceSound
open import Ordinal.Buchholz.OrderExtendedSound
open import Ordinal.Buchholz.RecursiveSurfaceBudget
open import Ordinal.Buchholz.SurfaceOrder
open import Ordinal.Buchholz.VeblenObligations
open import Ordinal.Buchholz.Smoke
