{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import MapArmv8toLIMM using (LIMM-Armv8Restricted)


module Proof.Mapping.Armv8toLIMM.Mapping
  (dst : Execution LabelLIMM)
  (dst-wf : WellFormed dst)
  (dst-ok : LIMM-Armv8Restricted dst)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Relation.Unary using (_∈_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.LIMM as LIMM
open import Arch.Armv8 as Armv8
-- Local imports: Theorem Specification
open import MapArmv8toLIMM
-- Local imports: Proof Components
import Proof.Framework LabelArmv8 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelArmv8 dst dst-wf as Δ
open import Proof.Mapping.Armv8toLIMM.Execution dst dst-wf dst-ok as PE -- defines `ev[⇐]` and `ψ`


open Ex.Execution
open LIMM-Armv8Restricted dst-ok


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Proof Components
open PE.Extra


-- Instrs: LD  ↦  LD;F_RM
-- Events: Rᵣ  ↦  Rᵣ;F_RM
src-rule-ld : {a : Event LabelArmv8}
  → {x : Location} {v : Value}
  → Armv8.EvR₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')
src-rule-ld a-r₌ a∈src =
  let a∈dst = events[⇒] a∈src
      (bᵗ , pi[ab]ᵗ , bᵗ-rm) = rᵣ-rmʳ a∈dst (Rₜ[⇒] a∈src (Armv8.r₌⇒rₜ a-r₌))
  in _ , _ , pi[ab]ᵗ , R₌[⇒] a∈src a-r₌ , bᵗ-rm


-- Instrs: LD_Q  ↦  LD;F_RM
-- Events: Qᵣ    ↦  Rᵣ;F_RM
src-rule-ldq : {a : Event LabelArmv8}
  → {x : Location} {v : Value}
  → Armv8.EvQ₌ x v a
  → a ∈ events src
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')
src-rule-ldq a-q₌ a∈src =
  let a∈dst = events[⇒] a∈src
      (bᵗ , pi[ab]ᵗ , bᵗ-rm) = rᵣ-rmʳ a∈dst (Rₜ[⇒] a∈src (q₌⇒rₜ a-q₌))
  in _ , _ , pi[ab]ᵗ , Q₌[⇒] a∈src a-q₌ , bᵗ-rm


-- Instrs: LD_A  ↦  LD;F_RM
-- Events: Aᵣ    ↦  Rᵣ;F_RM
src-rule-lda : {a : Event LabelArmv8}
  → {x : Location} {v : Value}
  → Armv8.EvA₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')
src-rule-lda a-a₌ a∈src =
  let a∈dst = events[⇒] a∈src
      (bᵗ , pi[ab]ᵗ , bᵗ-rm) = rᵣ-rmʳ a∈dst (Rₜ[⇒] a∈src (a₌⇒rₜ a-a₌))
  in _ , _ , pi[ab]ᵗ , A₌[⇒] a∈src a-a₌ , bᵗ-rm


-- Instrs: ST  ↦  STᵣ
-- Events: Wᵣ  ↦  Wᵣ
src-rule-st : {a : Event LabelArmv8}
  → {x : Location} {v : Value}
  → Armv8.EvW₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × LIMM.EvW₌ tmov x v a')
src-rule-st a-w₌ a∈src = _ , events[⇒] a∈src , W₌[⇒] a∈src a-w₌


-- Instrs: ST_L  ↦  F_WW;STᵣ;F_SC
-- Events: Lᵣ    ↦  F_WW;Wᵣ;F_SC
src-rule-stl : {b : Event LabelArmv8}
  → {x : Location} {v : Value}
  → Armv8.EvL₌ tmov x v b
  → b ∈ events src
  → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × po-imm dst b' c'
      × LIMM.EvF₌ WW a' × LIMM.EvW₌ tmov x v b' × LIMM.EvF₌ SC c')
src-rule-stl bˢ-l₌ b∈src =
  let b∈dst = events[⇒] b∈src
      bᵗ-org = l-org b∈dst (subst (EvLₜ tmov) (ev[⇒⇐] b∈src) (l₌⇒lₜ bˢ-l₌))
      (a , pi[ab] , a-ww) = l-wwˡ b∈dst bᵗ-org
      (c , pi[bc] , c-sc) = l-scʳ b∈dst bᵗ-org
  in _ , _ , _ , pi[ab] , pi[bc] , a-ww , L₌[⇒] b∈src bˢ-l₌ , c-sc


-- Instrs: RMW        ↦  RMW
-- Events: Rₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ
src-rule-rmw-ok : {a b : Event LabelArmv8}
  → {x : Location} {v₁ v₂ : Value}
  → Armv8.EvR₌ trmw x v₁ a
  → Armv8.EvW₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
src-rule-rmw-ok a-r₌ b-w₌ rmw[ab] =
  let a∈src = rmwˡ∈ex src-wf rmw[ab]
      b∈src = rmwʳ∈ex src-wf rmw[ab]
  in _ , _ , rmw[⇒] a∈src b∈src rmw[ab] , R₌[⇒] a∈src a-r₌ , W₌[⇒] b∈src b-w₌


src-rule-r-rmwˡ : {a : Event LabelArmv8}
  → {x : Location} {v : Value}
  → Armv8.EvR₌ trmw x v a
  → a ∈ dom (rmw src)
  → ∃[ a' ] a' ∈ dom (rmw dst) × LIMM.EvR₌ trmw x v a'
src-rule-r-rmwˡ a-r₌ a∈rmwˡ =
  let a∈src = rmwˡ∈ex src-wf (proj₂ a∈rmwˡ)
  in _ , rmwˡ[⇒] a∈src a∈rmwˡ , R₌[⇒] a∈src a-r₌


-- Instrs: RMW_A      ↦  RMW
-- Events: Aₐ;rmw;Wₐ  ↦  Rₐ;rmw;Wₐ
src-rule-rmw-a-ok : {a b : Event LabelArmv8}
  → {x : Location} {v₁ v₂ : Value}
  → Armv8.EvA₌ trmw x v₁ a
  → Armv8.EvW₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
src-rule-rmw-a-ok a-a₌ b-w₌ rmw[ab] =
  let a∈src = rmwˡ∈ex src-wf rmw[ab]
      b∈src = rmwʳ∈ex src-wf rmw[ab]
  in _ , _ , rmw[⇒] a∈src b∈src rmw[ab] , A₌[⇒] a∈src a-a₌ , W₌[⇒] b∈src b-w₌


src-rule-a-rmwˡ : {a : Event LabelArmv8}
  → {x : Location} {v : Value}
  → Armv8.EvA₌ trmw x v a
  → a ∈ dom (rmw src)
  → ∃[ a' ] a' ∈ dom (rmw dst) × LIMM.EvR₌ trmw x v a'
src-rule-a-rmwˡ a-a₌ a∈rmwˡ =
  let a∈src = rmwˡ∈ex src-wf (proj₂ a∈rmwˡ)
  in _ , rmwˡ[⇒] a∈src a∈rmwˡ , A₌[⇒] a∈src a-a₌


-- Instrs: RMW_L      ↦  RMW
-- Events: Rₐ;rmw;Lₐ  ↦  Rₐ;rmw;Wₐ
src-rule-rmw-l-ok : {a b : Event LabelArmv8}
  → {x : Location} {v₁ v₂ : Value}
  → Armv8.EvR₌ trmw x v₁ a
  → Armv8.EvL₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
src-rule-rmw-l-ok a-r₌ b-l₌ rmw[ab] =
  let a∈src = rmwˡ∈ex src-wf rmw[ab]
      b∈src = rmwʳ∈ex src-wf rmw[ab]
  in _ , _ , rmw[⇒] a∈src b∈src rmw[ab] , R₌[⇒] a∈src a-r₌ , L₌[⇒] b∈src b-l₌


-- Instrs: RMW_AL     ↦  RMW
-- Events: Aₐ;rmw;Lₐ  ↦  Rₐ;rmw;Lₐ
src-rule-rmw-al-ok : {a b : Event LabelArmv8}
  → {x : Location} {v₁ v₂ : Value}
  → Armv8.EvA₌ trmw x v₁ a
  → Armv8.EvL₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b'
src-rule-rmw-al-ok a-a₌ b-l₌ rmw[ab] =
  let a∈src = rmwˡ∈ex src-wf rmw[ab]
      b∈src = rmwʳ∈ex src-wf rmw[ab]
  in _ , _ , rmw[⇒] a∈src b∈src rmw[ab] , A₌[⇒] a∈src a-a₌ , L₌[⇒] b∈src b-l₌


-- Instrs: F_FULL  ↦  F_SC
-- Events: F_FULL  ↦  F_SC
src-rule-f-full : {a : Event LabelArmv8}
  → Armv8.EvF₌ F-full a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × LIMM.EvF₌ SC a')
src-rule-f-full a-f₌ a∈src =
  _ , events[⇒] a∈src , Ffull[⇒] a∈src a-f₌


-- Instrs: F_LD  ↦  skip
-- Events: F_LD  ↦  skip
src-rule-f-ld : {a : Event LabelArmv8}
  → Armv8.EvF₌ F-ld a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvSkip a')
src-rule-f-ld a-f₌ a∈src =
  _ , events[⇒] a∈src , Fld[⇒]skip a∈src a-f₌


-- Instrs: F_ISB  ↦  skip
-- Events: F_ISB  ↦  skip
src-rule-f-isb : {a : Event LabelArmv8}
  → Armv8.EvISB a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvSkip a')
src-rule-f-isb a-isb a∈src =
  _ , events[⇒] a∈src , ISB[⇒]skip a∈src a-isb


-- Instrs: F_ST  ↦  F_WW
-- Events: F_ST  ↦  F_WW
src-rule-f-st : {a : Event LabelArmv8}
  → Armv8.EvF₌ F-st a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × LIMM.EvF₌ WW a')
src-rule-f-st a-f₌ a∈src =
  _ , events[⇒] a∈src , Fst[⇒] a∈src a-f₌


src-mapping : Armv8⇒LIMM src dst
src-mapping =
  record
    { rule-ld        = src-rule-ld
    ; rule-ldq       = src-rule-ldq
    ; rule-lda       = src-rule-lda
    ; rule-st        = src-rule-st
    ; rule-stl       = src-rule-stl
    ; rule-rmw-ok    = src-rule-rmw-ok
    ; rule-r-rmwˡ    = src-rule-r-rmwˡ
    ; rule-rmw-a-ok  = src-rule-rmw-a-ok
    ; rule-a-rmwˡ    = src-rule-a-rmwˡ
    ; rule-rmw-l-ok  = src-rule-rmw-l-ok
    ; rule-rmw-al-ok = src-rule-rmw-al-ok
    ; rule-f-full    = src-rule-f-full
    ; rule-f-ld      = src-rule-f-ld
    ; rule-f-isb     = src-rule-f-isb
    ; rule-f-st      = src-rule-f-st
    }
