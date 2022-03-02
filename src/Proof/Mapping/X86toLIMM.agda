{-# OPTIONS --safe #-}

open import Arch.General.Execution
open import Arch.LIMM
open import MapX86toLIMM


module Proof.Mapping.X86toLIMM
  (dst : Execution LabelLIMM)
  (dst-wf : WellFormed dst)
  (dst-ok : LIMM-X86Restricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Library imports
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.X86
-- Local imports: Proofs
open import Proof.Mapping.X86toLIMM.Execution dst dst-wf dst-ok
open import Proof.Mapping.X86toLIMM.Consistent dst dst-wf dst-ok
open import Proof.Mapping.X86toLIMM.Mapping dst dst-wf dst-ok
import Proof.Mapping.Framework LabelX86 dst dst-wf as Δ


open LIMM-X86Restricted
open IsLIMMConsistent
open Δ.Definitions δ
open Δ.WellFormed δ
open Δ.Behavior δ


proof-X86⇒LIMM :
  ∃[ src ]
    ( WellFormed src
    × IsX86Consistent src
    × X86⇒LIMM src dst
    × behavior src ⇔₂ behavior dst
    )
proof-X86⇒LIMM =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , proof-behavior
  )
