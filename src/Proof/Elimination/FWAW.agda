{-# OPTIONS --safe #-}

-- Local imports: Architectures
open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
-- Local imports: Theorem Specification
open import TransformFWAW using (FWAW-Restricted)


-- | "Write-after-Write with Fence" elimination proof
module Proof.Elimination.FWAW
  (dst : Execution LabelLIMM)
  (dst-ok : FWAW-Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.LIMM
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import TransformFWAW using (FWAWMapping)
open import Proof.Elimination.FWAW.Execution dst dst-ok
open import Proof.Elimination.FWAW.WellFormed dst dst-ok
open import Proof.Elimination.FWAW.Consistent dst dst-ok
open import Proof.Elimination.FWAW.Mapping dst dst-ok
open import Proof.Elimination.FWAW.Behavior dst dst-ok
import Proof.Elimination.Framework dst dst-wf as Δ


open Δ.Definitions δ
open Arch.General.Execution


proof-FWAW :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × FWAWMapping src dst-ok
    × behavior src ⇔₂ behavior dst
    )
proof-FWAW =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , src-behavior
  )
