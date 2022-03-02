{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.X86 using (LabelX86)
open import MapLIMMtoX86 using (X86-LIMMRestricted)


module Proof.Mapping.LIMMtoX86.Execution
  (dst : Execution LabelX86)
  (dst-wf : WellFormed dst)
  (dst-ok : X86-LIMMRestricted dst)
  where


-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Unary using (Pred; _∈_; _∉_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution as Ex
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.X86 as X86
-- Local imports: Theorem Specification
open import MapLIMMtoArmv8
-- Local imports: Proof Components
import Proof.Framework LabelLIMM dst dst-wf as Ψ
import Proof.Mapping.Framework LabelLIMM dst dst-wf as Δ



open Ex.Execution
open X86-LIMMRestricted dst-ok



-- # Backward Mapping of Relations

-- The mapping:
--
-- Rᵣ(x,v)               ↦  Rᵣ(x,v)
-- Wᵣ(x,v)               ↦  Wᵣ(x,v)
-- Rₐ(x,v);rmw;Wₐ(x,v')  ↦  Rₐ(x,v);rmw;Wₐ(x,v')  || successful RMW
-- Rₐ(x,v)               ↦  Rₐ(x,v)               || failed RMW
-- F_SC                  ↦  F
-- F_RM / F_WW           ↦  skip


ev[⇐] : {x : Event LabelX86} → (x∈dst : x ∈ events dst) → Event LabelLIMM
ev[⇐] {event-init uid loc val} x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid}     x∈dst = event uid tid lemma
  where
  lemma : LabelLIMM
  lemma =
    case ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip) of
    λ{ (inj₁ _) → lab-f RM
     ; (inj₂ _) → lab-f WW
     }
ev[⇐] {event uid tid (lab-r tag loc val)} x∈dst = event uid tid (lab-r tag loc val)
ev[⇐] {event uid tid (lab-w tag loc val)} x∈dst = event uid tid (lab-w tag loc val)
ev[⇐] {event uid tid lab-f} x∈dst = event uid tid (lab-f SC)


-- # Proof framework

open Ψ.Definitions ev[⇐]

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐] {_} {event-init _ _ _}        x∈dst has-uid-init = has-uid-init
uid[⇐] {_} {event-skip _ _}          x∈dst has-uid-skip = has-uid
uid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid      = has-uid
uid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid      = has-uid
uid[⇐] {_} {event _ _ lab-f}         x∈dst has-uid      = has-uid

uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}        x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}          x∈dst has-uid      = has-uid-skip
uid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ lab-f}         x∈dst has-uid      = has-uid


tid[⇐] : {tid : UniqueId} → Pred[⇐]² (HasTid tid)
tid[⇐] {_} {event-skip _ _}          x∈dst has-tid-skip = has-tid
tid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ lab-f}         x∈dst has-tid = has-tid

tid[$⇒] : {tid : UniqueId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}          x∈dst has-tid = has-tid-skip
tid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid = has-tid
tid[$⇒] {_} {event _ _ lab-f}         x∈dst has-tid = has-tid


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] {_} {event-init _ _ _} x∈dst has-loc-init          = has-loc-init
loc[⇐] {_} {event _ _ _}      x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[⇐] {_} {event _ _ _}      x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl

loc[$⇒] : {loc : Location} → Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}        x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
loc[$⇒] {_} {event-skip _ _}          x∈dst x-loc | inj₁ _ = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))
loc[$⇒] {_} {event-skip _ _}          x∈dst x-loc | inj₂ _ = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))
loc[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-loc-r is-r refl) = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-loc-w is-w refl) = has-loc-w is-w refl
loc[$⇒] {_} {event _ _ lab-f}         x∈dst x-loc = ⊥-elim (¬f-loc (ev-f is-f) (_ , x-loc))


val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] {_} {event-init _ _ _} x∈dst has-val-init          = has-val-init
val[⇐] {_} {event _ _ _}      x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[⇐] {_} {event _ _ _}      x∈dst (has-val-w is-w refl) = has-val-w is-w refl

val[$⇒] : {val : Value} → Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}        x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
val[$⇒] {_} {event-skip _ _}          x∈dst x-val | inj₁ _ = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))
val[$⇒] {_} {event-skip _ _}          x∈dst x-val | inj₂ _ = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))
val[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (has-val-r is-r refl) = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (has-val-w is-w refl) = has-val-w is-w refl
val[$⇒] {_} {event _ _ lab-f}         x∈dst x-val = ⊥-elim (¬f-val (ev-f is-f) (_ , x-val))


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init

Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _}        x∈dst ev-init = ev-init
Init[$⇒] {event-skip _ _}          x∈dst ()
Init[$⇒] {event _ _ (lab-r _ _ _)} x∈dst ()
Init[$⇒] {event _ _ (lab-w _ _ _)} x∈dst ()
Init[$⇒] {event _ _ lab-f}         x∈dst ()


Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐] x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] x∈dst (ev-w is-w refl) = ev-w is-w refl


Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _}        x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
Wₜ[$⇒] {_} {event-skip _ _}          x∈dst (ev-w () _) | inj₁ _
Wₜ[$⇒] {_} {event-skip _ _}          x∈dst (ev-w () _) | inj₂ _
Wₜ[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (ev-w () _)
Wₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-w is-w refl) = ev-w is-w refl
Wₜ[$⇒] {_} {event _ _ lab-f}         x∈dst (ev-w () _)


Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] x∈dst (ev-r is-r refl) = ev-r is-r refl

Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
Rₜ[$⇒] {_} {event-skip _ _}          x∈dst (ev-r () _) | inj₁ _
Rₜ[$⇒] {_} {event-skip _ _}          x∈dst (ev-r () _) | inj₂ _
Rₜ[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst (ev-r is-r refl) = ev-r is-r refl
Rₜ[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst (ev-r () _)
Rₜ[$⇒] {_} {event _ _ lab-f}         x∈dst (ev-r () _)


ψ : Ψ.GeneralFramework
ψ =
  record
    { ev[⇐]    = ev[⇐]
    ; uid[⇐]   = uid[⇐]
    ; uid[$⇒]  = uid[$⇒]
    ; tid[⇐]   = tid[⇐]
    ; tid[$⇒]  = tid[$⇒]
    ; Init[⇐]  = Init[⇐]
    ; Init[$⇒] = Init[$⇒]
    }

δ : Δ.MappingFramework
δ =
  record
    { ψ       = ψ
    ; loc[⇐]  = loc[⇐]
    ; loc[$⇒] = loc[$⇒]
    ; val[⇐]  = val[⇐]
    ; val[$⇒] = val[$⇒]
    ; Wₜ[⇐]   = Wₜ[⇐]
    ; Wₜ[$⇒]  = Wₜ[$⇒]
    ; Rₜ[⇐]   = Rₜ[⇐]
    ; Rₜ[$⇒]  = Rₜ[$⇒]
    }


-- # Extra helpers

module Extra where

  open Δ.Definitions δ
  open Ψ.WellFormed ψ using (rmw[⇒])


  F[$⇒] : Pred[$⇒] (EvF₌ SC) EvF
  F[$⇒] {event-skip _ _}  x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  F[$⇒] {event-skip _ _}  x∈dst () | inj₁ _
  F[$⇒] {event-skip _ _}  x∈dst () | inj₂ _
  F[$⇒] {event _ _ lab-f} x∈dst ev-f₌ = ev-f is-f
  
  F[⇒] : Pred[⇒] (EvF₌ SC) EvF
  F[⇒] = [$⇒]→₁[⇒] F[$⇒]


  R₌[$⇒] : {tag : Tag} {x : Location} {v : Value} → Pred[$⇒] (LIMM.EvR₌ tag x v) (X86.EvR₌ tag x v)
  R₌[$⇒] {_} {_} {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  R₌[$⇒] {_} {_} {_} {event-skip _ _}          x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event-skip _ _}          x∈dst () | inj₂ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r _ _ _)} x∈dst ev-r₌ = ev-r

  R₌[⇒] : {tag : Tag} {x : Location} {v : Value} → Pred[⇒] (LIMM.EvR₌ tag x v) (X86.EvR₌ tag x v)
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]
  

  W₌[$⇒] : {tag : Tag} {x : Location} {v : Value} → Pred[$⇒] (LIMM.EvW₌ tag x v) (X86.EvW₌ tag x v)
  W₌[$⇒] {_} {_} {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  W₌[$⇒] {_} {_} {_} {event-skip _ _}          x∈dst () | inj₁ _
  W₌[$⇒] {_} {_} {_} {event-skip _ _}          x∈dst () | inj₂ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w _ _ _)} x∈dst ev-w₌ = ev-w₌

  W₌[⇒] : {tag : Tag} {x : Location} {v : Value} → Pred[⇒] (LIMM.EvW₌ tag x v) (X86.EvW₌ tag x v)
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]
  

  Frm[$⇒]skip : Pred[$⇒] (EvF₌ RM) EvSkip
  Frm[$⇒]skip {event-skip _ _}  x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  Frm[$⇒]skip {event-skip _ _}  x∈dst ev-f₌ | inj₁ _ = ev-skip
  Frm[$⇒]skip {event _ _ lab-f} x∈dst ()
  
  Frm[⇒]skip : Pred[⇒] (EvF₌ RM) EvSkip
  Frm[⇒]skip = [$⇒]→₁[⇒] Frm[$⇒]skip
  

  Fww[$⇒]skip : Pred[$⇒] (EvF₌ WW) EvSkip
  Fww[$⇒]skip {event-skip _ _}  x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  Fww[$⇒]skip {event-skip _ _}  x∈dst ev-f₌ | inj₂ _ = ev-skip
  Fww[$⇒]skip {event _ _ lab-f} x∈dst ()
  
  Fww[⇒]skip : Pred[⇒] (EvF₌ WW) EvSkip
  Fww[⇒]skip = [$⇒]→₁[⇒] Fww[$⇒]skip
