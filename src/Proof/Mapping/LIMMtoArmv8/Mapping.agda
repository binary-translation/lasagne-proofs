{-# OPTIONS --safe #-}


open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.Armv8 using (LabelArmv8)
open import MapLIMMtoArmv8 using (Armv8-LIMMRestricted)


-- | This proof component produces `LIMM⇒Armv8`, which relates the source and
-- target executions.
--
-- Note that `Proof.Mapping.LIMMtoArmv8.Execution` /defines/ the source execution
-- from the target. Here we /relate/ them.
module Proof.Mapping.LIMMtoArmv8.Mapping
  (dst : Execution LabelArmv8)
  (dst-wf : WellFormed dst)
  (dst-ok : Armv8-LIMMRestricted dst)
  where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Relation.Nullary using (¬_)
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
open import Arch.Armv8 as Armv8
-- Local imports: Theorem Specification
open import MapLIMMtoArmv8
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Mapping.Framework LabelLIMM dst dst-wf as Δ
open import Proof.Mapping.LIMMtoArmv8.Execution dst dst-wf dst-ok as PE -- defines `ev[⇐]` and `ψ`


open Execution
open WellFormed
open IsArmv8Consistent
open Armv8-LIMMRestricted dst-ok


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ
-- Proof Components
open PE.Extra



private
  dst-consistent = consistent
  dst-a8 = a8 dst-consistent


-- Instrs: LD      ↦ LDR
-- Events: Rᵣ(x,v) ↦ Rᵣ(x,v)
src-rule-ld : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
  → LIMM.EvR₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ tmov x v a')
src-rule-ld a-r₌ a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r₌


-- Instrs: ST      ↦ STR
-- Events: Wᵣ(x,v) ↦ W(x,v)ᵣ
src-rule-st : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
  → LIMM.EvW₌ tmov x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ tmov x v a')
src-rule-st a-w₌ a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w₌


-- Instrs: RMW ↦ DMBFF;RMW;DMBFF
-- Events: Rₗ;rmw;Wₗ  ↦ F_FULL;Rₗ;lxsx;Wₗ;F_FULL  || successful RMW
--         Rₗ         ↦ F_FULL;Rₗ;F_FULL          || failed RMW

src-rule-rmw-dom : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
  → LIMM.EvR₌ trmw x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvR₌ trmw x v a')
src-rule-rmw-dom a-r₌ a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , R₌[⇒] a∈src a-r₌

src-rule-rmw-codom : ∀ {a : Event LabelLIMM} {x : Location} {v : Value}
  → LIMM.EvW₌ trmw x v a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvW₌ trmw x v a')
src-rule-rmw-codom a-w₌ a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , W₌[⇒] a∈src a-w₌


src-rule-rmw-ok : ∀ {a b c d : Event LabelLIMM} {x : Location} {v₁ v₂ : Value}
  → EvSkip a
  → LIMM.EvR₌ trmw x v₁ b
  → LIMM.EvW₌ trmw x v₂ c
  → EvSkip d
  → po-imm src a b
  → rmw src b c
  → po-imm src c d
  → ∃[ a' ] ∃[ b' ] ∃[ c' ] ∃[ d' ] (po-imm dst a' b' × rmw dst b' c' × po-imm dst c' d'
      × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v₁ b' × Armv8.EvW₌ trmw x v₂ c' × Armv8.EvF₌ F-full d')
src-rule-rmw-ok {a} {b} {c} {d} a-skip b-r c-w d-skip pi[ab] rmw[bc] pi[cd] =
  ev[⇒] a∈src , ev[⇒] b∈src , ev[⇒] c∈src , ev[⇒] d∈src ,
    pi[⇒] a∈src b∈src pi[ab] , rmw[⇒] b∈src c∈src rmw[bc] , pi[⇒] c∈src d∈src pi[cd] ,
    pre-ff , R₌[⇒] b∈src b-r , W₌[⇒] c∈src c-w , post-ff
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
  c∈src = poˡ∈src (proj₁ pi[cd])
  d∈src = poʳ∈src (proj₁ pi[cd])
  ¬init-c : ¬ EvInit (ev[⇒] c∈src)
  ¬init-c c-init = disjoint-wₜ _ (init⇒wₜ (Init[⇐$] c∈src c-init) , w₌⇒wₜ c-w)
  pre-ff : Armv8.EvF₌ F-full (ev[⇒] {a} a∈src)
  pre-ff with rmw-ff-l (events[⇒] b∈src) (Rₜ[⇒] b∈src (LIMM.r₌⇒rₜ b-r))
    where
    b-rt : EvRₜ trmw (ev[⇒] b∈src)
    b-rt = Rₜ[⇒] b∈src (×₂-applyˡ (rmw-r×w src-wf) rmw[bc])
  ... | w , pi[wb] , w-org =
    -- Somehow, matching `w≡a` to `refl` hangs typechecking forever
    let w≡a = po-immˡ dst-wf pi[wb] (pi[⇒] a∈src b∈src pi[ab])
    in org-f-pre-rmw-f dst-ok (subst org-f-pre-rmw w≡a w-org)
  post-ff : Armv8.EvF₌ F-full (ev[⇒] {d} d∈src)
  post-ff with rmw-ff-r-ok (rmw[⇒] b∈src c∈src rmw[bc])
  ... | w , pi[cw] , w-org =
    -- Somehow, matching `w≡d` to `refl` hangs typechecking forever
    let w≡d = po-immʳ dst-wf ¬init-c pi[cw] (pi[⇒] c∈src d∈src pi[cd])
    in org-f-post-rmw-f dst-ok (subst org-f-post-rmw w≡d w-org)

src-rule-rmw-fail : ∀ {a b c : Event LabelLIMM} {x : Location} {v : Value}
  → EvSkip a
  → LIMM.EvR₌ trmw x v b
  → EvSkip c
  → po-imm src a b
  → b ∉ dom (rmw src)
  → po-imm src b c
  → ∃[ a' ] ∃[ b' ] ∃[ c' ] (po-imm dst a' b' × b' ∉ dom (rmw dst) × po-imm dst b' c'
      × Armv8.EvF₌ F-full a' × Armv8.EvR₌ trmw x v b' × Armv8.EvF₌ F-full c')
src-rule-rmw-fail {a} {b} {c} a-skip b-r c-skip pi[ab] b∉rmwˡ pi[bc] =
  ev[⇒] a∈src , ev[⇒] b∈src , ev[⇒] c∈src ,
    pi[⇒] a∈src b∈src pi[ab] , ¬rmwˡ[⇒] b∈src b∉rmwˡ , pi[⇒] b∈src c∈src pi[bc] ,
    pre-ff , R₌[⇒] b∈src b-r , post-ff
  where
  a∈src = poˡ∈src (proj₁ pi[ab])
  b∈src = poʳ∈src (proj₁ pi[ab])
  c∈src = poʳ∈src (proj₁ pi[bc])
  ¬init-b : ¬ EvInit (ev[⇒] b∈src)
  ¬init-b b-init = disjoint-r/init _ (rₜ⇒r (LIMM.r₌⇒rₜ b-r) , Init[⇐$] b∈src b-init)
  pre-ff : Armv8.EvF₌ F-full (ev[⇒] {a} a∈src)
  pre-ff with rmw-ff-l (events[⇒] b∈src) (Rₜ[⇒] b∈src (LIMM.r₌⇒rₜ b-r))
  ... | w , pi[wb] , w-org =
    -- Somehow, matching `w≡a` to `refl` hangs typechecking forever
    let w≡a = po-immˡ dst-wf pi[wb] (pi[⇒] a∈src b∈src pi[ab])
    in org-f-pre-rmw-f dst-ok (subst org-f-pre-rmw w≡a w-org)
  post-ff : Armv8.EvF₌ F-full (ev[⇒] {c} c∈src)
  post-ff with rmw-ff-r-fail (events[⇒] b∈src) (Rₜ[⇒] b∈src (LIMM.r₌⇒rₜ b-r)) (¬rmwˡ[⇒] b∈src b∉rmwˡ)
  ... | w , pi[bw] , w-org =
    -- Somehow, matching `w≡c` to `refl` hangs typechecking forever
    let w≡c = po-immʳ dst-wf ¬init-b pi[bw] (pi[⇒] b∈src c∈src pi[bc])
    in org-f-post-rmw-f dst-ok (subst org-f-post-rmw w≡c w-org)


-- Instrs: F_LD_ST ↦ DMBLD
-- Events: F_RM    ↦ F_LD
src-rule-f-rm : ∀ {a : Event LabelLIMM}
  → LIMM.EvF₌ RM a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-ld a')
src-rule-f-rm a-rm a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , Frm[⇒] a∈src a-rm


-- Instrs: F_ST_ST ↦ DMBST
-- Events: F_WW    ↦ F_ST
src-rule-f-ww : ∀ {a : Event LabelLIMM}
  → LIMM.EvF₌ WW a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-st a')
src-rule-f-ww a-ww a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , Fww[⇒] a∈src a-ww


-- Instrs: F_SC ↦ DMBFF
-- Events: F_SC ↦ F
src-rule-f-sc : ∀ {a : Event LabelLIMM}
  → LIMM.EvF₌ SC a
  → a ∈ events src
  → ∃[ a' ] (a' ∈ events dst × Armv8.EvF₌ F-full a')
src-rule-f-sc a-f a∈src =
  ev[⇒] a∈src , events[⇒] a∈src , Fsc[⇒] a∈src a-f


src-mapping : LIMM⇒Armv8 src dst-a8
src-mapping =
  record
    { rule-ld        = src-rule-ld
    ; rule-st        = src-rule-st
    ; rule-rmw-dom   = src-rule-rmw-dom
    ; rule-rmw-codom = src-rule-rmw-codom
    ; rule-rmw-ok    = src-rule-rmw-ok
    ; rule-rmw-fail  = src-rule-rmw-fail
    ; rule-f-rm      = src-rule-f-rm
    ; rule-f-ww      = src-rule-f-ww
    ; rule-f-sc      = src-rule-f-sc
    }
