{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import MapX86toLIMM using (LIMM-X86Restricted)


module Proof.Mapping.X86toLIMM.Mapping
  (dst : Execution LabelLIMM)
  (dst-wf : WellFormed dst)
  (dst-ok : LIMM-X86Restricted dst)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Relation.Unary using (_∈_; _∉_)
-- Library imports
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.X86 as X86
-- Local imports: Theorem Specification
open import MapX86toLIMM
-- Local imports: Proof Components
import Proof.Framework LabelX86 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelX86 dst dst-wf as Δ
open import Proof.Mapping.X86toLIMM.Execution dst dst-wf dst-ok as PE -- defines `ev[⇐]` and `ψ`


open Execution
open LIMM-X86Restricted dst-ok


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Proof Components
open PE.Extra


-- Instrs: RMOV    ↦ LD;F_LD_M
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v);F_RM
src-rule-rmov : ∀ {a b : Event LabelX86} {x : Location} {v : Value}
  → X86.EvR₌ tmov x v a
  → EvSkip b
  → po-imm src a b
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvR₌ tmov x v a' × LIMM.EvF₌ RM b')
src-rule-rmov {a} {b} ev-r b-skip pi[ab] with r-f-po₁ (events[⇒] {a} a∈src) (Rₜ[⇒] a∈src (ev-r is-r refl))
  where a∈src = poˡ∈src (proj₁ pi[ab])
... | z , pi[az] , z-is-f =
  let a∈src = poˡ∈src (proj₁ pi[ab])
      b∈src = poʳ∈src (proj₁ pi[ab])
      -- Matching `z≡b` to `refl` makes typechecking take forever
      z≡b = po-immʳ dst-wf (¬Init[⇒] a∈src (λ{q → disjoint-r/init _ (ev-r is-r , q)})) pi[az] (pi[⇒] a∈src b∈src pi[ab])
  in _ , _ , pi[⇒] a∈src b∈src pi[ab] , R₌[⇒] a∈src ev-r , subst (EvF₌ RM) z≡b z-is-f


-- Instrs: WMOV   ↦ F_ST_ST;ST
-- Events: W(x,v) ↦ F_WW;W(x,v)
src-rule-wmov : ∀ {a b : Event LabelX86}
    {x : Location} {v : Value}
  → EvSkip a
  → X86.EvW₌ tmov x v b
  → po-imm src a b
  → ∃[ a' ] ∃[ b' ] (po-imm dst a' b' × LIMM.EvF₌ WW a' × LIMM.EvW₌ tmov x v b')
src-rule-wmov {a} {b} ev-skip ev-w₌ pi[ab]
  with f-w-po₁ {ev[⇒] {a} a∈src} (events[⇒] {b} b∈src) (Wₜ[⇒] b∈src (ev-w is-w refl))
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
... | z , pi[zb] , z-is-f =
  let a∈src = poˡ∈src (proj₁ pi[ab])
      b∈src = poʳ∈src (proj₁ pi[ab])
      -- Matching `z≡a` to `refl` makes typechecking take forever
      z≡a = po-immˡ dst-wf pi[zb] (pi[⇒] {a} {b} a∈src b∈src pi[ab])
  in _ , _ , pi[⇒] a∈src b∈src pi[ab] , subst (EvF₌ WW) z≡a z-is-f , W₌[⇒] b∈src ev-w₌
  

-- Instrs: RMW ↦ RMW
-- Events: Rₗ(x,v);rmw;W(x,v') ↦ Rₗ(x,v);rmw;W(x,v')  || successful
--         Rₗ(x,v)             ↦ Rₗ(x,v)              || failed
src-rule-rmw-ok : ∀ {a b : Event LabelX86}
    {x : Location} {v₁ v₂ : Value}
  → X86.EvR₌ trmw x v₁ a
  → X86.EvW₌ trmw x v₂ b
  → rmw src a b
  → ∃[ a' ] ∃[ b' ] (rmw dst a' b' × LIMM.EvR₌ trmw x v₁ a' × LIMM.EvW₌ trmw x v₂ b')
src-rule-rmw-ok {a} {b} ev-r ev-w₌ rmw[ab] =
  let a∈src = rmwˡ∈src rmw[ab]
      b∈src = rmwʳ∈src rmw[ab]
  in ev[⇒] a∈src , ev[⇒] b∈src , rmw[⇒] a∈src b∈src rmw[ab] , R₌[⇒] a∈src ev-r , W₌[⇒] b∈src ev-w₌

src-rule-rmw-fail₁ : ∀ {a b : Event LabelX86}
    {x : Location} {v : Value}
  → X86.EvR₌ trmw x v a
  → po src a b
  → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvR₌ trmw x v a')
src-rule-rmw-fail₁ {a} {b} ev-r po[ab] =
  let a∈src = poˡ∈src po[ab]
      b∈src = poʳ∈src po[ab]
  in ev[⇒] {a} a∈src , ev[⇒] {b} b∈src , po[⇒] {a} {b} a∈src b∈src po[ab] , R₌[⇒] a∈src ev-r


src-rule-rmw-fail₂ : ∀ {a b : Event LabelX86}
    {x : Location} {v : Value}
  → X86.EvR₌ trmw x v b
  → po src a b
  → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvR₌ trmw x v b')
src-rule-rmw-fail₂ {a} {b} ev-r po[ab] =
  let a∈src = poˡ∈src po[ab]
      b∈src = poʳ∈src po[ab]
  in ev[⇒] {a} a∈src , ev[⇒] {b} b∈src , po[⇒] {a} {b} a∈src b∈src po[ab] , R₌[⇒] b∈src ev-r


-- Instrs: MFENCE ↦ F_SC
-- Events: F      ↦ F_SC
src-rule-fence₁ : ∀ {a b : Event LabelX86}
  → EvF a
  → po src a b
  → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvF₌ LIMM.SC a')
src-rule-fence₁ {a} {b} (ev-f is-f) po[ab] =
  let a∈src = poˡ∈src po[ab]
      b∈src = poʳ∈src po[ab]
  in ev[⇒] {a} a∈src , ev[⇒] {b} b∈src , po[⇒] {a} {b} a∈src b∈src po[ab] , F[⇒] a∈src (ev-f is-f)


src-rule-fence₂ : ∀ {a b : Event LabelX86}
  → EvF b
  → po src a b
  → ∃[ a' ] ∃[ b' ] (po dst a' b' × LIMM.EvF₌ LIMM.SC b')
src-rule-fence₂ {a} {b} (ev-f is-f) po[ab] =
  let a∈src = poˡ∈src po[ab]
      b∈src = poʳ∈src po[ab]
  in ev[⇒] {a} a∈src , ev[⇒] {b} b∈src , po[⇒] {a} {b} a∈src b∈src po[ab] , F[⇒] b∈src (ev-f is-f)


src-mapping : X86⇒LIMM src dst
src-mapping =
  record
    { rule-rmov      = src-rule-rmov
    ; rule-wmov      = src-rule-wmov
    ; rule-rmw-ok    = src-rule-rmw-ok
    ; rule-rmw-fail₁ = src-rule-rmw-fail₁
    ; rule-rmw-fail₂ = src-rule-rmw-fail₂
    ; rule-fence₁    = src-rule-fence₁
    ; rule-fence₂    = src-rule-fence₂
    }
