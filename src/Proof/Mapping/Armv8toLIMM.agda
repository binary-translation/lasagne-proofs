{-# OPTIONS --safe #-}

open import Arch.General.Execution
open import Arch.LIMM
open import MapArmv8toLIMM


module Proof.Mapping.Armv8toLIMM
  (dst : Execution LabelLIMM)
  (dst-wf : WellFormed dst)
  (dst-ok : LIMM-Armv8Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Library imports
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.Armv8
-- Local imports: Proof Components
open import Proof.Mapping.Armv8toLIMM.Execution dst dst-wf dst-ok
open import Proof.Mapping.Armv8toLIMM.Consistent dst dst-wf dst-ok
open import Proof.Mapping.Armv8toLIMM.Mapping dst dst-wf dst-ok
import Proof.Mapping.Framework LabelArmv8 dst dst-wf as Δ


open LIMM-Armv8Restricted
open IsLIMMConsistent
open Δ.Definitions δ
open Δ.WellFormed δ
open Δ.Behavior δ


proof-Armv8⇒LIMM :
  ∃[ src ]
    ( WellFormed src
    × IsArmv8Consistent src
    × Armv8⇒LIMM src dst
    × behavior src ⇔₂ behavior dst
    )
proof-Armv8⇒LIMM =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , proof-behavior
  )
