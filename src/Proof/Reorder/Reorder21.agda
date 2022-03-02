{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder21 using (ReorderRestricted21)


-- | Reorders two events with one event
--
-- > (a ∘ b) ∘ c  →  c ∘ (a ∘ b)
--
--
-- Particularly, this reorders the instructions:
--
-- > RMW ; F  →  F ; RMW
--
-- For /any/ fence. The proof considers the case where this RMW is /successful/.
-- Failed RMWs are handled by `Proof.Reorder.Single`.
module Proof.Reorder.Reorder21
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted21 dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; swap; ∃-syntax)
-- Library imports
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.LIMM
-- Local imports: Theorem Specification
open import TransformReorder21
-- Local imports: Proof Components
open import Proof.Reorder.Reorder21.Execution dst dst-res
open import Proof.Reorder.Reorder21.WellFormed dst dst-res
open import Proof.Reorder.Reorder21.Consistent dst dst-res
open import Proof.Reorder.Reorder21.Mapping dst dst-res


--
-- For reordering proofs, the tricky parts pertain to `po`.
-- The other relations (including the otherwise difficult GHB relation)
-- follow naturally.
--


proof-reorder21 :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × ReordersTo21 src dst-res
    × behavior src ⇔₂ behavior dst
    )
proof-reorder21 =
  ( src
  , src-wf
  , src-consistent
  , proof-mapping
  , ≡-to-⇔₂ refl -- trivial. co src ≡ co dst
  )
