{-# OPTIONS --safe #-}

-- | LIMM ⇒ Armv8 mapping specification
module MapLIMMtoArmv8 where

-- Stdlib imports
open import Level using () renaming (zero to ℓzero)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; ∃-syntax; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (_∷_; [])
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
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
open WellFormed


--
-- + Mapping - LIMM ⇒ ARMv8
--
-- ++ Instruction mapping:
--
-- LD       ↦  LDR
-- ST       ↦  STR
-- RMW      ↦  DMBFF;RMW;DMBFF
-- F_LD_M   ↦  DMBLD
-- F_ST_ST  ↦  DMBST
-- F_SC     ↦  DMBFF
--
--
-- ++ Corresponding event mapping:
--
-- Rᵣ         ↦  Rᵣ
-- Wᵣ         ↦  Wᵣ
-- Rₗ;rmw;Wₗ  ↦  F_FULL;Rₗ;rmw;Wₗ;F_FULL  || successful RMW
-- Rₗ         ↦  F_FULL;Rₗ;F_FULL         || failed RMW
-- F_RM       ↦  F_LD
-- F_WW       ↦  F_ST
-- F_SC       ↦  F_FULL
--

-- Armv8 programs mapped from LIMM can only contain:
-- R W F_LD F_ST F_FULL
data IsArmv8EventLIMM : Event LabelArmv8 → Set where
  ev-init : {uid : UniqueId} {loc : Location} {val : Value} → IsArmv8EventLIMM (event-init uid loc val)
  ev-skip : {uid : UniqueId} {tid : ThreadId} → IsArmv8EventLIMM (event-skip uid tid)
  ev-r    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → IsArmv8EventLIMM (event uid tid (lab-r tag loc val))
  ev-w    : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → IsArmv8EventLIMM (event uid tid (lab-w tag loc val))
  ev-f    : {uid : UniqueId} {tid : ThreadId} {mode : Armv8.F-mode} → IsArmv8EventLIMM (event uid tid (lab-f mode))


-- | A proof that a Armv8 execution could only have been generated from a Armv8 program
-- that is mapped from an LIMM program.
--
-- This follows from mappings on the instruction-level. (Which we omit)
record Armv8-LIMMRestricted (ex : Execution LabelArmv8) : Set₁ where
  field
    consistent : IsArmv8Consistent ex
    
    ev-bound : events ex ⊆₁ IsArmv8EventLIMM

    -- Denotes where the events originate in the target. If the mapping were defined on the
    -- /instruction level/, it is obvious where /instructions/ in the target come from.
    -- However, as the instructions are absent in our model, we annotate events accordingly.
    
    -- origins: full
    org-f-sc       : Pred (Event LabelArmv8) ℓzero
    org-f-pre-rmw  : Pred (Event LabelArmv8) ℓzero
    org-f-post-rmw : Pred (Event LabelArmv8) ℓzero
    -- origins: load fence - can only be created from `RM` fences.
    -- origins: skip - can only be created from skips
    -- origins: store fence - can only be created from `WW` fences

    -- Before every RMW-read there is a full fence
    rmw-ff-l : ∀ {b : Event LabelArmv8} → b ∈ events ex → EvRₜ trmw b → ∃[ a ] (po-imm ex a b × org-f-pre-rmw a)
    -- After every successful-RMW-write there is a full fence
    rmw-ff-r-ok : ∀ {a b : Event LabelArmv8} → rmw ex a b → ∃[ c ] (po-imm ex b c × org-f-post-rmw c)
    -- After every failed-RMW-read there is a full fence
    rmw-ff-r-fail : ∀ {a : Event LabelArmv8} → a ∈ events ex → EvRₜ trmw a → a ∉ dom (rmw ex) → ∃[ b ] (po-imm ex a b × org-f-post-rmw b)

    org-f-def : (events ex ∩₁ Armv8.EvF₌ F-full) ⇔₁ (org-f-pre-rmw ∪₁ org-f-post-rmw ∪₁ org-f-sc)
    
    disjoint-f   : PairwiseDisjoint₁ (org-f-sc ∷ org-f-pre-rmw ∷ org-f-post-rmw ∷ [])

open Armv8-LIMMRestricted


-- | Relates the events in the source and target executions, following the
-- mapping on the instructions.
record LIMM⇒Armv8 (src : Execution LabelLIMM) {dst : Execution LabelArmv8} (dst-a8 : Armv8Execution dst) : Set where
  field
    -- Instrs: LD ↦ LDR
    -- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
    rule-ld : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
      → LIMM.EvR₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ tmov x v a')


    -- Instrs: ST ↦ STR
    -- Events: Wᵣ(x,v) ↦ W(x,v)ᵣ
    rule-st : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
      → LIMM.EvW₌ tmov x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ tmov x v a')


    -- Instrs: RMW ↦ DMBFF;RMW;DMBFF
    -- Events: Rₗ;rmw;Wₗ  ↦ F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
    --         Rₗ         ↦ F_FULL;Rₗ;F_FULL          || failed RMW

    rule-rmw-dom : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
      → LIMM.EvR₌ trmw x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ trmw x v a')
    rule-rmw-codom : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
      → LIMM.EvW₌ trmw x v a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ trmw x v a')
    rule-rmw-ok : ∀ {a b c d : Event LabelLIMM} {x : Location} {v₁ v₂ : Value}
      → EvSkip a
      → LIMM.EvR₌ trmw x v₁ b
      → LIMM.EvW₌ trmw x v₂ c
      → EvSkip d
      → po-imm src a b
      → rmw src b c
      → po-imm src c d
      → ∃[ a' ] ∃[ b' ] ∃[ c' ] ∃[ d' ] (po-imm dst a' b' × rmw dst b' c' × po-imm dst c' d'
          × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v₁ b' × Armv8.EvW₌ trmw x v₂ c' × Armv8.EvF₌ F-full d')
    rule-rmw-fail : ∀ {a b c : Event LabelLIMM} {x : Location} {v : Value}
      → EvSkip a
      → LIMM.EvR₌ trmw x v b
      → EvSkip c
      → po-imm src a b
      → b ∉ dom (rmw src)
      → po-imm src b c
      → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × b' ∉ dom (rmw dst) × po-imm dst b' c'
          × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v b' × Armv8.EvF₌ F-full c')


    -- Instrs: F_LD_M ↦ DMBLD
    -- Events: F_RM  ↦ F_LD
    rule-f-rm : ∀ {a : Event LabelLIMM}
      → LIMM.EvF₌ RM a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-ld a')


    -- Instrs: F_ST_ST ↦ DMBST
    -- Events: F_WW    ↦ F_ST
    rule-f-ww : ∀ {a : Event LabelLIMM}
      → LIMM.EvF₌ WW a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-st a')


    -- Instrs: F_SC ↦ DMBFF
    -- Events: F_SC ↦ F
    rule-f-sc : ∀ {a : Event LabelLIMM}
      → LIMM.EvF₌ SC a
      → a ∈ events src
      → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-full a')


-- # Helpers

¬ev-bound : {ex : Execution LabelArmv8} (ex-res : Armv8-LIMMRestricted ex) {ev : Event LabelArmv8} → ev ∈ events ex → ¬ (IsArmv8EventLIMM ev) → ⊥
¬ev-bound ex-res ev∈ex ¬is-a8 = ¬is-a8 (⊆₁-apply (ev-bound ex-res) ev∈ex)

po-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-LIMMRestricted ex)
  → po ex ⊆₂ IsArmv8EventLIMM ×₂ IsArmv8EventLIMM
po-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (⇔₁-to-⊆₁ (po-elements wf))) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))

rf-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-LIMMRestricted ex)
  → rf ex ⊆₂ IsArmv8EventLIMM ×₂ IsArmv8EventLIMM
rf-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (rf-elements wf)) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))
  
co-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-LIMMRestricted ex)
  → co ex ⊆₂ IsArmv8EventLIMM ×₂ IsArmv8EventLIMM
co-bound {ex} wf ex-res =
  ⊆₂-trans (×₂-lift-udr (co-elements wf)) (×₂-lift (ev-bound ex-res) (ev-bound ex-res))
  
rmw-bound : {ex : Execution LabelArmv8} (wf : WellFormed ex) (ex-res : Armv8-LIMMRestricted ex)
  → rmw ex ⊆₂ IsArmv8EventLIMM ×₂ IsArmv8EventLIMM
rmw-bound wf ex-res = ⊆₂-trans (rmw-def wf) (⊆₂-trans imm-⊆₂ (po-bound wf ex-res))

org-f-pre-rmw-f : {ex : Execution LabelArmv8} (ex-res : Armv8-LIMMRestricted ex)
  → {x : Event LabelArmv8}
  → org-f-pre-rmw ex-res x
  → Armv8.EvF₌ F-full x
org-f-pre-rmw-f ex-res x-pre = proj₂ (⇔₁-apply-⊇₁ (org-f-def ex-res) (inj₁ (inj₁ x-pre)))

org-f-post-rmw-f : {ex : Execution LabelArmv8} (ex-res : Armv8-LIMMRestricted ex)
  → {x : Event LabelArmv8}
  → org-f-post-rmw ex-res x
  → Armv8.EvF₌ F-full x
org-f-post-rmw-f ex-res x-post = proj₂ (⇔₁-apply-⊇₁ (org-f-def ex-res) (inj₁ (inj₂ x-post)))
