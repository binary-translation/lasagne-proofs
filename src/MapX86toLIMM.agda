{-# OPTIONS --safe #-}

module MapX86toLIMM where

-- Stdlib imports
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Unary using (Pred; _∈_)
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

--
-- Mapping - X86 ⇒ LIMM
--
--
-- Instruction mapping:
--
-- RMOV   ↦ LD;F_LD_M
-- WMOV   ↦ F_ST_ST;ST
-- RMW    ↦ RMW
-- MFENCE ↦ F_SC
--
-- Corresponding event mapping:
--
-- Rᵣ(x,v)             ↦ Rᵣ(x,v);F_RM
-- W(x,v)              ↦ F_WW;Wᵣ(x,v)
-- Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;Wₗ(x,v')  || successful RMW
-- Rₗ(x,v)             ↦ Rₗ(x,v)               || failed RMW
-- F                   ↦ F_SC
--

-- | A proof that a LIMM execution could only have been generated from a LIMM program
-- that is mapped from an X86 program.
--
-- This follows from mappings on the instruction-level. (Which we omit)
record LIMM-X86Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    consistent : IsLIMMConsistent ex
    
    -- Read events that are generated from the LD instruction are /always/ followed by a F_RM fence.
    -- By the rule: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
    -- There is no other way of obtaining a Rᵣ event.
    r-f-po₁ : ∀ {a : Event LabelLIMM} → a ∈ events ex → EvRₜ tmov a → ∃[ b ] (po-imm ex a b × LIMM.EvF₌ RM b)
    r-f-po₂ : ∀ {b : Event LabelLIMM} → b ∈ events ex → LIMM.EvF₌ RM b → ∃[ a ] (po-imm ex a b × EvRₜ tmov a)

    -- Rule: W(x,v) ↦ F_WW;W(x,v)
    -- Every non-rmw write (ST) is preceded by a F_WW event
    f-w-po₁ : ∀ {a b : Event LabelLIMM} → b ∈ events ex → EvWₜ tmov b → ∃[ a ] (po-imm ex a b × LIMM.EvF₌ WW a)
    -- Every F_WW event is followed by a W event
    f-w-po₂ : ∀ {a b : Event LabelLIMM} → a ∈ events ex → LIMM.EvF₌ WW a → ∃[ b ] (po-imm ex a b × EvWₜ tmov b)

open LIMM-X86Restricted


-- | Relates the events in the source and target executions, following the
-- mapping on the instructions.
record X86⇒LIMM (src : Execution LabelX86) (dst : Execution LabelLIMM) : Set where
  field
    -- Instrs: RMOV    ↦ LD;F_LD_M
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
    rule-rmov : ∀ {a b : Event LabelX86} {x : Location} {v : Value}
      → X86.EvR₌ tmov x v a
      → EvSkip b
      → po-imm src a b
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')

    -- Instrs: WMOV   ↦ F_ST_ST;ST
    -- Events: W(x,v) ↦ F_WW;W(x,v)
    rule-wmov : ∀ {a b : Event LabelX86}
        {x : Location} {v : Value}
      → EvSkip a
      → X86.EvW₌ tmov x v b
      → po-imm src a b
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvF₌ WW a' × LIMM.EvW₌ tmov x v b')

    -- Instrs: RMW ↦ RMW
    -- Events: Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;W(x,v')  || successful
    --         Rₗ(x,v)             ↦ Rₗ(x,v)              || failed
    rule-rmw-ok : ∀ {a b : Event LabelX86}
        {x : Location} {v₁ v₂ : Value}
      → X86.EvR₌ trmw x v₁ a
      → X86.EvW₌ trmw x v₂ b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b')
      
    rule-rmw-fail₁ : ∀ {a b : Event LabelX86}
        {x : Location} {v : Value}
      → X86.EvR₌ trmw x v a
      → po src a b
      → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvR₌ trmw x v a')
    rule-rmw-fail₂ : ∀ {a b : Event LabelX86}
        {x : Location} {v : Value}
      → X86.EvR₌ trmw x v b
      → po src a b
      → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvR₌ trmw x v b')

    -- Instrs: MFENCE ↦ F_SC
    -- Events: F      ↦ F_SC
    rule-fence₁ : ∀ {a b : Event LabelX86}
      → EvF a
      → po src a b
      → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvF₌ LIMM.SC a')
    rule-fence₂ : ∀ {a b : Event LabelX86}
      → EvF b
      → po src a b
      → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvF₌ LIMM.SC b')
