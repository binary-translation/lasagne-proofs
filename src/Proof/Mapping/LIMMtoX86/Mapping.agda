{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.X86 using (LabelX86)
open import MapLIMMtoX86 using (X86-LIMMRestricted)


module Proof.Mapping.LIMMtoX86.Mapping
  (dst : Execution LabelX86)
  (dst-wf : WellFormed dst)
  (dst-ok : X86-LIMMRestricted dst)
  where

-- Stdlib imports
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Library imports
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
-- open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.X86 as X86
-- Local imports: Theorem Specification
open import MapLIMMtoX86
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Mapping.Framework LabelLIMM dst dst-wf as Δ
open import Proof.Mapping.LIMMtoX86.Execution dst dst-wf dst-ok as PE


open Ex.Execution
open PE.Extra


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ


-- Instrs: LDᵣ      ↦  LD
-- Events: Rᵣ(x,v)  ↦  Rᵣ(x,v)
src-rule-ld : {a : Event LabelLIMM} {x : Location} {v : Value}
  → LIMM.EvR₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × X86.EvR₌ tmov x v a')
src-rule-ld a-r₌ a∈src =
  _ , events[⇒] a∈src , R₌[⇒] a∈src a-r₌


-- Instrs: STᵣ      ↦  ST
-- Events: Wᵣ(x,v)  ↦  Wᵣ(x,v)
src-rule-st : {a : Event LabelLIMM} {x : Location} {v : Value}
  → LIMM.EvW₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × X86.EvW₌ tmov x v a')
src-rule-st a-w₌ a∈src =
  _ , events[⇒] a∈src , W₌[⇒] a∈src a-w₌


-- Instrs: RMW                   ↦  RMW
-- Events: Rₐ(x,v);rmw;Wₐ(x,v')  ↦  Rₐ(x,v);rmw;Wₐ(x,v')  || successful RMW
src-rule-rmw-ok : {a b : Event LabelLIMM} {x : Location} {v₁ v₂ : Value}
  → LIMM.EvR₌ trmw x v₁ a
  → LIMM.EvW₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × X86.EvR₌ trmw x v₁ a' × X86.EvW₌ trmw x v₂ b')
src-rule-rmw-ok a-r₌ b-w₌ rmw[ab] =
  let a∈src = rmwˡ∈ex src-wf rmw[ab]
      b∈src = rmwʳ∈ex src-wf rmw[ab]
  in _ , _ , rmw[⇒] a∈src b∈src rmw[ab] , R₌[⇒] a∈src a-r₌ , W₌[⇒] b∈src b-w₌


-- Instrs: RMW      ↦  RMW
-- Events: Rₐ(x,v)  ↦  Rₐ(x,v)  || failed RMW
src-rule-rmw-fail : {a : Event LabelLIMM} {x : Location} {v : Value}
  → LIMM.EvR₌ trmw x v a
  → a ∈ events src
  → a ∉ dom (rmw src)
  → ∃[ a' ] (a' ∈ events dst × a' ∉ dom (rmw dst) × X86.EvR₌ trmw x v a')
src-rule-rmw-fail a-r₌ a∈src a∉rmwˡ =
  _ , events[⇒] a∈src , ¬rmwˡ[⇒] a∈src a∉rmwˡ , R₌[⇒] a∈src a-r₌


-- Instrs: F_SC  ↦  MFENCE
-- Events: F_SC  ↦  F
src-rule-fsc : {a : Event LabelLIMM}
  → LIMM.EvF₌ SC a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvF a')
src-rule-fsc a-sc a∈src =
  _ , events[⇒] a∈src , F[⇒] a∈src a-sc


-- Instrs: F_RM  ↦  skip
-- Events: F_RM  ↦  skip
src-rule-frm : {a : Event LabelLIMM}
  → LIMM.EvF₌ RM a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvSkip a')
src-rule-frm a-rm a∈src =
  _ , events[⇒] a∈src , Frm[⇒]skip a∈src a-rm


-- Instrs: F_WW  ↦  skip
-- Events: F_WW  ↦  skip
src-rule-fww : {a : Event LabelLIMM}
  → LIMM.EvF₌ WW a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × EvSkip a')
src-rule-fww a-ww a∈src =
  _ , events[⇒] a∈src , Fww[⇒]skip a∈src a-ww


src-mapping : LIMM⇒X86 src dst
src-mapping =
  record
    { rule-ld       = src-rule-ld
    ; rule-st       = src-rule-st
    ; rule-rmw-ok   = src-rule-rmw-ok
    ; rule-rmw-fail = src-rule-rmw-fail
    ; rule-fsc      = src-rule-fsc
    ; rule-frm      = src-rule-frm
    ; rule-fww      = src-rule-fww
    }
