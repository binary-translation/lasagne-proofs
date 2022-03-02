{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformRAW using (RAW-Restricted)


-- | Read-after-Write elimination proof
module Proof.Elimination.RAW
  (dst : Execution LabelLIMM)
  (dst-ok : RAW-Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.LIMM
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import TransformRAW using (RAWMapping)
open import Proof.Elimination.RAW.Execution dst dst-ok
open import Proof.Elimination.RAW.WellFormed dst dst-ok
open import Proof.Elimination.RAW.Consistent dst dst-ok
open import Proof.Elimination.RAW.Mapping dst dst-ok
open import Proof.Elimination.RAW.Behavior dst dst-ok
import Proof.Elimination.Framework dst dst-wf as Δ


open Δ.Definitions δ
open Arch.General.Execution


proof-RAW :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × RAWMapping src dst-ok
    × behavior src ⇔₂ behavior dst
    )
proof-RAW =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , src-behavior
  )
