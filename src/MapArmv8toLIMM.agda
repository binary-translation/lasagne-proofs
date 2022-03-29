{-# OPTIONS --safe #-}


-- | Armv8 ⇒ LIMM mapping specification
module MapArmv8toLIMM where

-- Stdlib imports
open import Level using () renaming (zero to ℓzero)
open import Data.Product using (_×_; ∃-syntax)
open import Relation.Unary using (Pred; _∈_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.LIMM as LIMM
open import Arch.Armv8 as Armv8


open Execution


--
-- + Mapping - Armv8 ⇒ LIMM
--
-- ++ Instruction mapping:
--
-- LD / LD_Q / LD_A  ↦  LD;F_RM
-- ST                ↦  STᵣ
-- ST_L              ↦  F_WW;STᵣ;F_SC
-- RMW / RMW_A|L|AL  ↦  RMW
-- F_FULL            ↦  F_SC
-- F_LD / F_ISB      ↦  skip
-- F_ST              ↦  F_WW
--
--
-- ++ Corresponding event mapping:
--
-- Rᵣ / Aᵣ / Qᵣ              ↦  Rᵣ;F_RM
-- Wᵣ                        ↦  Wᵣ
-- Lᵣ                        ↦  F_WW;Wᵣ;F_SC
-- Rₐ;rmw;Wₐ / Aₐ;rmw;Wₐ
--   / Rₐ;rmw;Lₐ / Aₐ;rmw;Lₐ ↦  Rₐ;rmw;Wₐ  || successful RMW
-- Rₐ / Aₐ                   ↦  Rₐ         || failed RMW
-- F_FULL                    ↦  F_SC
-- F_LD / F_ISB              ↦  skip
-- F_ST                      ↦  F_WW
--


-- | Demonstrates the LIMM execution was produced by a LIMM program mapped from
-- an Armv8 program.
record LIMM-Armv8Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    consistent : IsLIMMConsistent ex
    
    -- Denotes where the events originate in the target. If the mapping were defined on the
    -- /instruction level/, it is obvious where /instructions/ in the target come from.
    -- However, as the instructions are absent in our model, we annotate events accordingly.

    -- origins: Rᵣ (relaxed reads)
    org-rᵣ-r : Pred (Event LabelLIMM) ℓzero -- Rᵣ ↦ Rᵣ;F_RM
    org-rᵣ-q : Pred (Event LabelLIMM) ℓzero -- Qᵣ ↦ Rᵣ;F_RM
    org-rᵣ-a : Pred (Event LabelLIMM) ℓzero -- Aᵣ ↦ Rᵣ;F_RM

    -- origins: Wᵣ (relaxed writes)
    org-wᵣ-w : Pred (Event LabelLIMM) ℓzero -- Wᵣ ↦ Wᵣ
    org-wᵣ-l : Pred (Event LabelLIMM) ℓzero -- Lᵣ ↦ F_WW;Wᵣ;F_SC

    -- origins: Rₐ (atomic reads)
    org-rₐ-r : Pred (Event LabelLIMM) ℓzero -- Rₐ ↦ Rₐ
    org-rₐ-a : Pred (Event LabelLIMM) ℓzero -- Aₐ ↦ Rₐ

    -- origins: Wₐ (atomic writes)
    org-wₐ-w : Pred (Event LabelLIMM) ℓzero -- Wₐ ↦ Wₐ
    org-wₐ-l : Pred (Event LabelLIMM) ℓzero -- Lₐ ↦ Wₐ

    -- origins: F_WW
    org-ww-l : Pred (Event LabelLIMM) ℓzero -- Lᵣ   ↦ F_WW;Wᵣ;F_SC
    org-ww-f : Pred (Event LabelLIMM) ℓzero -- F_ST ↦ F_WW

    -- origins: F_SC
    org-sc-l : Pred (Event LabelLIMM) ℓzero -- Lᵣ     ↦ F_WW;Wᵣ;F_SC
    org-sc-f : Pred (Event LabelLIMM) ℓzero -- F_FULL ↦ F_SC

    -- origins: Skip
    org-skip-fld  : Pred (Event LabelLIMM) ℓzero -- F_LD  ↦ skip
    org-skip-isb  : Pred (Event LabelLIMM) ℓzero -- F_ISB ↦ skip
    org-skip-skip : Pred (Event LabelLIMM) ℓzero -- skip  ↦ skip

    -- Every relaxed read is followed by a RM fence
    rᵣ-rmʳ : ∀ {x : Event LabelLIMM} → x ∈ events ex → EvRₜ tmov x → ∃[ y ] (po-imm ex x y × LIMM.EvF₌ RM y)
    rᵣ-rmˡ : ∀ {y : Event LabelLIMM} → y ∈ events ex → LIMM.EvF₌ RM y → ∃[ x ] (po-imm ex x y × EvRₜ tmov x)

    -- ST_L  →  F_WW;STᵣ;F_SC
    l-wwˡ : ∀ {y : Event LabelLIMM} → y ∈ events ex → org-wᵣ-l y → ∃[ x ] (po-imm ex x y × LIMM.EvF₌ WW x)
    l-scʳ : ∀ {x : Event LabelLIMM} → x ∈ events ex → org-wᵣ-l x → ∃[ y ] (po-imm ex x y × LIMM.EvF₌ SC y)

    -- Some restrictions are missing, but they're not needed for the proof anyway.
    -- (Note that we never produce a `LIMM-Armv8Restricted`, only consume it)

    org-rᵣ   : (events ex ∩₁ EvRₜ tmov)    ⇔₁ OptPred₃ org-rᵣ-r org-rᵣ-q org-rᵣ-a
    org-wᵣ   : (events ex ∩₁ EvWₜ tmov)    ⇔₁ org-wᵣ-w ∪₁ org-wᵣ-l
    org-rₐ   : (events ex ∩₁ EvRₜ trmw)    ⇔₁ org-rₐ-r ∪₁ org-rₐ-a
    org-wₐ   : (events ex ∩₁ EvWₜ trmw)    ⇔₁ org-wₐ-w ∪₁ org-wₐ-l
    org-ww   : (events ex ∩₁ LIMM.EvF₌ WW) ⇔₁ org-ww-l ∪₁ org-ww-f
    org-sc   : (events ex ∩₁ LIMM.EvF₌ SC) ⇔₁ org-sc-l ∪₁ org-sc-f
    org-skip : (events ex ∩₁ EvSkip)       ⇔₁ OptPred₃ org-skip-fld org-skip-isb org-skip-skip


-- | Relates the events in the source and target executions, following the
-- mapping on the instructions.
record Armv8⇒LIMM (src : Execution LabelArmv8) (dst : Execution LabelLIMM) : Set where
  field
    -- Instrs: LD  ↦  LD;F_RM
    -- Events: Rᵣ  ↦  Rᵣ;F_RM
    rule-ld : {a : Event LabelArmv8}
      → {x : Location} {v : Value}
      → Armv8.EvR₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')
    
    -- Instrs: LD_Q  ↦  LD;F_RM
    -- Events: Qᵣ    ↦  Rᵣ;F_RM
    rule-ldq : {a : Event LabelArmv8}
      → {x : Location} {v : Value}
      → Armv8.EvQ₌ x v a
      → a ∈ events src
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')
    
    -- Instrs: LD_A  ↦  LD;F_RM
    -- Events: Aᵣ    ↦  Rᵣ;F_RM
    rule-lda : {a : Event LabelArmv8}
      → {x : Location} {v : Value}
      → Armv8.EvA₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')

    -- Instrs: ST  ↦  STᵣ
    -- Events: Wᵣ  ↦  Wᵣ
    rule-st : {a : Event LabelArmv8}
      → {x : Location} {v : Value}
      → Armv8.EvW₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × LIMM.EvW₌ tmov x v a')
    
    -- Instrs: ST_L  ↦  F_WW;STᵣ;F_SC
    -- Events: Lᵣ    ↦  F_WW;Wᵣ;F_SC
    rule-stl : {b : Event LabelArmv8}
      → {x : Location} {v : Value}
      → Armv8.EvL₌ tmov x v b
      → b ∈ events src
      → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × po-imm dst b' c'
          × LIMM.EvF₌ WW a' × LIMM.EvW₌ tmov x v b' × LIMM.EvF₌ SC c')

    -- Instrs: RMW        ↦  RMW
    -- Events: Rₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ
    rule-rmw-ok : {a b : Event LabelArmv8}
      → {x : Location} {v₁ v₂ : Value}
      → Armv8.EvR₌ trmw x v₁ a
      → Armv8.EvW₌ trmw x v₂ b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
    rule-r-rmwˡ : {a : Event LabelArmv8}
      → {x : Location} {v : Value}
      → Armv8.EvR₌ trmw x v a
      → a ∈ dom (rmw src)
      → ∃[ a' ] a' ∈ dom (rmw dst) × LIMM.EvR₌ trmw x v a'

    -- Instrs: RMW_A      ↦  RMW
    -- Events: Aₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ
    rule-rmw-a-ok : {a b : Event LabelArmv8}
      → {x : Location} {v₁ v₂ : Value}
      → Armv8.EvA₌ trmw x v₁ a
      → Armv8.EvW₌ trmw x v₂ b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
    rule-a-rmwˡ : {a : Event LabelArmv8}
      → {x : Location} {v : Value}
      → Armv8.EvA₌ trmw x v a
      → a ∈ dom (rmw src)
      → ∃[ a' ] a' ∈ dom (rmw dst) × LIMM.EvR₌ trmw x v a'
    
    -- Instrs: RMW_L      ↦  RMW
    -- Events: Rₐ;rmw;Lₐ  ↦  Rₐ;rmw;Wₐ
    rule-rmw-l-ok : {a b : Event LabelArmv8}
      → {x : Location} {v₁ v₂ : Value}
      → Armv8.EvR₌ trmw x v₁ a
      → Armv8.EvL₌ trmw x v₂ b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
    -- failed case is `rule-r-rmwˡ`
    
    -- Instrs: RMW_AL     ↦  RMW
    -- Events: Aₐ;rmw;Lₐ  ↦  Rₐ;rmw;Lₐ
    rule-rmw-al-ok : {a b : Event LabelArmv8}
      → {x : Location} {v₁ v₂ : Value}
      → Armv8.EvA₌ trmw x v₁ a
      → Armv8.EvL₌ trmw x v₂ b
      → rmw src a b
      → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
    -- failed case is `rule-a-rmwˡ`
    

    -- Instrs: F_FULL  ↦  F_SC
    -- Events: F_FULL  ↦  F_SC
    rule-f-full : {a : Event LabelArmv8}
      → Armv8.EvF₌ F-full a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × LIMM.EvF₌ SC a')
    
    -- Instrs: F_LD  ↦  skip
    -- Events: F_LD  ↦  skip
    rule-f-ld : {a : Event LabelArmv8}
      → Armv8.EvF₌ F-ld a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvSkip a')
    
    -- Instrs: F_ISB  ↦  skip
    -- Events: F_ISB  ↦  skip
    rule-f-isb : {a : Event LabelArmv8}
      → Armv8.EvISB a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × EvSkip a')

    -- Instrs: F_ST  ↦  F_WW
    -- Events: F_ST  ↦  F_WW
    rule-f-st : {a : Event LabelArmv8}
      → Armv8.EvF₌ F-st a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × LIMM.EvF₌ WW a')
