{-# OPTIONS --safe #-}

-- | LIMM ⇒ X86 mapping specification
module MapLIMMtoX86 where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Data.Product using (_×_; ∃-syntax)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.X86 as X86
open import Arch.LIMM as LIMM


open Execution


-- # Definitions

-- Mapping - LIMM ⇒ X86
--
--
-- Instruction mapping:
--
-- LDᵣ          ↦  LD
-- STᵣ          ↦  ST
-- RMW          ↦  RMW
-- F_SC         ↦  MFENCE
-- F_RM / F_WW  ↦  skip
--
-- Corresponding event mapping:
--
-- Rᵣ(x,v)               ↦  Rᵣ(x,v)
-- Wᵣ(x,v)               ↦  Wᵣ(x,v)
-- Rₐ(x,v);rmw;Wₐ(x,v')  ↦  Rₐ(x,v);rmw;Wₐ(x,v')  || successful RMW
-- Rₐ(x,v)               ↦  Rₐ(x,v)               || failed RMW
-- F_SC                  ↦  F
-- F_RM / F_WW           ↦  skip



-- | A proof that a X86 execution could only have been generated from a LIMM program
-- that is mapped to a X86 program.
--
-- This follows from mappings on the instruction-level. (Which we omit)
record X86-LIMMRestricted (ex : Execution LabelX86) : Set₁ where
  field
    consistent : IsX86Consistent ex

    -- F_RM / F_WW           ↦  skip
    org-skip-frm : Pred (Event LabelX86) ℓzero
    org-skip-fww : Pred (Event LabelX86) ℓzero
    
    org-skip : (events ex ∩₁ EvSkip) ⇔₁ org-skip-frm ∪₁ org-skip-fww



-- | Relates the events in the source and target executions, following the
-- mapping on the instructions.
record LIMM⇒X86 (src : Execution LabelLIMM) (dst : Execution LabelX86) : Set where
  field
  
    -- Instrs: LDᵣ      ↦  LD
    -- Events: Rᵣ(x,v)  ↦  Rᵣ(x,v)
    rule-ld : {a : Event LabelLIMM} {x : Location} {v : Value}
      → LIMM.EvR₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × X86.EvR₌ tmov x v a')

    -- Instrs: STᵣ      ↦  ST
    -- Events: Wᵣ(x,v)  ↦  Wᵣ(x,v)
    rule-st : {a : Event LabelLIMM} {x : Location} {v : Value}
      → LIMM.EvW₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × X86.EvW₌ tmov x v a')

    -- Instrs: RMW                   ↦  RMW
    -- Events: Rₐ(x,v);rmw;Wₐ(x,v')  ↦  Rₐ(x,v);rmw;Wₐ(x,v')  || successful RMW
    rule-rmw-ok : {a b : Event LabelLIMM} {x : Location} {v₁ v₂ : Value}
      → LIMM.EvR₌ trmw x v₁ a
      → LIMM.EvW₌ trmw x v₂ b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × X86.EvR₌ trmw x v₁ a' × X86.EvW₌ trmw x v₂ b')
      
    -- Instrs: RMW      ↦  RMW
    -- Events: Rₐ(x,v)  ↦  Rₐ(x,v)  || failed RMW
    rule-rmw-fail : {a : Event LabelLIMM} {x : Location} {v : Value}
      → LIMM.EvR₌ trmw x v a
      → a ∈ events src
      → a ∉ dom (rmw src)
      → ∃[ a' ] (a' ∈ events dst × a' ∉ dom (rmw dst) × X86.EvR₌ trmw x v a')
      

    -- Instrs: F_SC  ↦  MFENCE
    -- Events: F_SC  ↦  F
    rule-fsc : {a : Event LabelLIMM}
      → LIMM.EvF₌ SC a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvF a')
      

    -- Instrs: F_RM  ↦  skip
    -- Events: F_RM  ↦  skip
    rule-frm : {a : Event LabelLIMM}
      → LIMM.EvF₌ RM a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvSkip a')


    -- Instrs: F_WW  ↦  skip
    -- Events: F_WW  ↦  skip
    rule-fww : {a : Event LabelLIMM}
      → LIMM.EvF₌ WW a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvSkip a')
