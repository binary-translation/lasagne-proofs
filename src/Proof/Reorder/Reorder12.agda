{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder12 using (ReorderRestricted12)


-- | Reorders one event with two events.
--
-- > a ∘ (b ∘ c)  →  (b ∘ c) ∘ a
--
--
-- Particularly, this reorders the instructions:
--
-- > F ; RMW  →  RMW ; F
--
-- For /any/ fence. The proof considers the case where this RMW is /successful/.
-- Failed RMWs are handled by `Proof.Reorder.Single`.
module Proof.Reorder.Reorder12
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted12 dst)
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
open import TransformReorder12
-- Local imports: Proof Components
open import Proof.Reorder.Reorder12.Execution dst dst-res
open import Proof.Reorder.Reorder12.WellFormed dst dst-res
open import Proof.Reorder.Reorder12.Consistent dst dst-res
open import Proof.Reorder.Reorder12.Mapping dst dst-res


--
-- For reordering proofs, the tricky parts pertain to `po`.
-- The other relations (including the otherwise difficult GHB relation)
-- follow naturally.
--


proof-reorder12 :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × ReordersTo12 src dst-res
    × behavior src ⇔₂ behavior dst
    )
proof-reorder12 =
  ( src
  , src-wf
  , src-consistent
  , proof-mapping
  , ≡-to-⇔₂ refl -- trivial. co src ≡ co dst
  )
