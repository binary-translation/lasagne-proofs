{-# OPTIONS --safe #-}

open import Arch.General.Execution
open import Arch.X86
open import MapLIMMtoX86


module Proof.Mapping.LIMMtoX86
  (dst : Execution LabelX86)
  (dst-wf : WellFormed dst)
  (dst-ok : X86-LIMMRestricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; ∃-syntax)
-- Library imports
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.LIMM
-- Local imports: Proofs
open import Proof.Mapping.LIMMtoX86.Execution dst dst-wf dst-ok
open import Proof.Mapping.LIMMtoX86.Consistent dst dst-wf dst-ok
open import Proof.Mapping.LIMMtoX86.Mapping dst dst-wf dst-ok
import Proof.Mapping.Framework LabelLIMM dst dst-wf as Δ


open X86-LIMMRestricted
open IsX86Consistent
open Δ.Definitions δ
open Δ.WellFormed δ
open Δ.Behavior δ


proof-LIMM⇒X86 :
  ∃[ src ]
    ( WellFormed src
    × IsLIMMConsistent src
    × LIMM⇒X86 src dst
    × behavior src ⇔₂ behavior dst
    )
proof-LIMM⇒X86 =
  ( src
  , src-wf
  , src-consistent
  , src-mapping
  , proof-behavior
  )
