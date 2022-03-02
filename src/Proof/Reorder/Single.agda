{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformReorder using (ReorderRestricted)


-- | Reorders two individual events
--
-- > a ∘ b  →  b ∘ a
--
-- (Note that this is in contrast to multiple reorders like `(a ∘ b) ∘ c  →  c ∘ (a ∘ b)`)
module Proof.Reorder.Single
  (dst : Execution LabelLIMM)
  (dst-res : ReorderRestricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Library imports
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.LIMM
-- Local imports: Theorem Specification
open import TransformReorder
-- Local imports: Proof Components
open import Proof.Reorder.Single.Execution dst dst-res
open import Proof.Reorder.Single.WellFormed dst dst-res
open import Proof.Reorder.Single.Consistent dst dst-res
open import Proof.Reorder.Single.Mapping dst dst-res


--
-- The table of valid reorders proved by this description. ("X" means valid)
-- Note that the holes are covered by the rules in `ReorderRestricted`.
-- (See also `TransformRestricted`)
--
-- a \ b | Rᵣ    | Wᵣ    | Rₐ    | F_RM  | F_WW  | F_SC
-- ------+-------+-------+-------+-------+-------+-----
-- Rᵣ    | X     | X     | X     |       | X     |  
-- Wᵣ    | X     | X     | X     | X     |       |  
-- Rₐ    |       |       |       | X     | X     | X
-- F_RM  |       |       |       | X     | X     | X
-- F_WW  | X     |       | X     | X     | X     | X
-- F_SC  |       |       |       | X     | X     | X
--

--
-- For reordering proofs, the tricky parts pertain to `po`.
-- The other relations (including the otherwise difficult GHB relation)
-- follow naturally.
--

proof-reorder :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × ReordersTo src dst-res
    × behavior src ⇔₂ behavior dst
    )
proof-reorder =
  ( src
  , src-wf
  , src-consistent
  , proof-mapping
  , ≡-to-⇔₂ refl -- trivial. co src ≡ co dst
  )
