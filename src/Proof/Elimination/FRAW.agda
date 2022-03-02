{-# OPTIONS --safe #-}

-- Local imports: Architectures
open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
-- Local imports: Theorem Specification
open import TransformFRAW using (FRAW-Restricted)


-- | "Read-after-Write with Fence" elimination proof
module Proof.Elimination.FRAW
  (dst : Execution LabelLIMM)
  (dst-ok : FRAW-Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.LIMM
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import TransformFRAW using (FRAWMapping)
open import Proof.Elimination.FRAW.Execution dst dst-ok
open import Proof.Elimination.FRAW.WellFormed dst dst-ok
open import Proof.Elimination.FRAW.Consistent dst dst-ok
open import Proof.Elimination.FRAW.Mapping dst dst-ok
open import Proof.Elimination.FRAW.Behavior dst dst-ok
import Proof.Elimination.Framework dst dst-wf as Δ


open Δ.Definitions δ
open Arch.General.Execution


proof-FRAW :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × FRAWMapping src dst-ok
    × behavior src ⇔₂ behavior dst
    )
proof-FRAW =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , src-behavior
  )
