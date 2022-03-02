{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import TransformRAR using (RAR-Restricted)


-- | Read-after-Read elimination proof
module Proof.Elimination.RAR
  (dst : Execution LabelLIMM)
  (dst-ok : RAR-Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Local imports: Architectures
open import Arch.General.Execution
open import Arch.LIMM
-- Local imports: Relations
open import Dodo.Binary
-- Local imports: Proofs
open import TransformRAR using (RARMapping)
open import Proof.Elimination.RAR.Execution dst dst-ok
open import Proof.Elimination.RAR.WellFormed dst dst-ok
open import Proof.Elimination.RAR.Consistent dst dst-ok
open import Proof.Elimination.RAR.Mapping dst dst-ok
open import Proof.Elimination.RAR.Behavior dst dst-ok
import Proof.Elimination.Framework dst dst-wf as Δ


open Δ.Definitions δ
open Arch.General.Execution


proof-RAR :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × RARMapping src dst-ok
    × behavior src ⇔₂ behavior dst
    )
proof-RAR =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , src-behavior
  )
