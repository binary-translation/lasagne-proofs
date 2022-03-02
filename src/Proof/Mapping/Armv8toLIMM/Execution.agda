{-# OPTIONS --safe #-}


open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import MapArmv8toLIMM using (LIMM-Armv8Restricted)


module Proof.Mapping.Armv8toLIMM.Execution
  (dst : Execution LabelLIMM)
  (dst-wf : WellFormed dst)
  (dst-ok : LIMM-Armv8Restricted dst)
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
-- Local imports: Helpers
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution as Ex
open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.Armv8 as Armv8
-- Local imports: Theorem Specification
open import MapArmv8toLIMM
-- Local imports: Proof Components
import Proof.Framework LabelArmv8 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelArmv8 dst dst-wf as Δ


open Ex.Execution
open LIMM-Armv8Restricted dst-ok


-- # Backward Mapping of Relations

ev[⇐] : {x : Event LabelLIMM}
  → (x∈dst : x ∈ events dst)
    ------------------------
  → Event LabelArmv8
ev[⇐] {event-init uid loc val} x∈dst = event-init uid loc val
ev[⇐] {event-skip uid tid} x∈dst with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
... | opt₁ _ = event uid tid (lab-f F-ld) -- org-skip-fld
... | opt₂ _ = event uid tid lab-isb      -- org-skip-isb
... | opt₃ _ = event-skip uid tid         -- org-skip-skip
ev[⇐] {event uid tid (lab-r tag loc val)} x∈dst =
  event uid tid lemma
  where
  lemma : LabelArmv8
  lemma with inspect tag
  lemma | tmov with≡ refl with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  lemma | tmov with≡ refl | opt₁ _ = lab-r tmov loc val -- org-rᵣ-r
  lemma | tmov with≡ refl | opt₂ _ = lab-q loc val      -- org-rᵣ-q
  lemma | tmov with≡ refl | opt₃ _ = lab-a tmov loc val -- org-rᵣ-a
  lemma | trmw with≡ refl with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  lemma | trmw with≡ refl | inj₁ _ = lab-r trmw loc val -- org-rₐ-r
  lemma | trmw with≡ refl | inj₂ _ = lab-a trmw loc val -- org-rₐ-a
ev[⇐] {event uid tid (lab-w tag loc val)} x∈dst = event uid tid lemma
  where
  lemma : LabelArmv8
  lemma with inspect tag
  lemma | tmov with≡ refl with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  lemma | tmov with≡ refl | inj₁ _ = lab-w tmov loc val -- org-wᵣ-w
  lemma | tmov with≡ refl | inj₂ _ = lab-l tmov loc val -- org-wᵣ-l
  lemma | trmw with≡ refl with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  lemma | trmw with≡ refl | inj₁ _ = lab-w trmw loc val -- org-wₐ-w
  lemma | trmw with≡ refl | inj₂ _ = lab-l trmw loc val -- org-wₐ-l
ev[⇐] {event uid tid (lab-f RM)} x∈dst = event-skip uid tid -- LD;F_RM
ev[⇐] {event uid tid (lab-f WW)} x∈dst with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
... | inj₁ _ = event-skip uid tid -- org-ww-l
... | inj₂ _ = event uid tid (lab-f F-st) -- org-ww-f
ev[⇐] {event uid tid (lab-f SC)} x∈dst with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
... | inj₁ _ = event-skip uid tid -- org-sc-l
... | inj₂ _ = event uid tid (lab-f F-full) -- org-sc-f


-- # Proof framework

open Ψ.Definitions ev[⇐]

uid[⇐] : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
uid[⇐] x∈dst has-uid-init = has-uid-init
uid[⇐] x∈dst has-uid-skip with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
... | opt₁ _ = has-uid
... | opt₂ _ = has-uid
... | opt₃ _ = has-uid-skip
uid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid = has-uid
uid[⇐] {_} {event _ _ (lab-f RM)}    x∈dst has-uid = has-uid-skip
uid[⇐] {_} {event _ _ (lab-f WW)}    x∈dst has-uid with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
... | inj₁ _ = has-uid-skip
... | inj₂ _ = has-uid
uid[⇐] {_} {event _ _ (lab-f SC)}    x∈dst has-uid with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
... | inj₁ _ = has-uid-skip
... | inj₂ _ = has-uid

uid[$⇒] : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
uid[$⇒] {_} {event-init _ _ _}        x∈dst has-uid-init = has-uid-init
uid[$⇒] {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
uid[$⇒] {_} {event-skip _ _}          x∈dst has-uid      | opt₁ _ = has-uid-skip
uid[$⇒] {_} {event-skip _ _}          x∈dst has-uid      | opt₂ _ = has-uid-skip
uid[$⇒] {_} {event-skip _ _}          x∈dst has-uid-skip | opt₃ _ = has-uid-skip
uid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-uid      = has-uid
uid[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst has-uid-skip = has-uid
uid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
uid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-uid-skip | inj₁ _ = has-uid
uid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-uid      | inj₂ _ = has-uid
uid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
uid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-uid-skip | inj₁ _ = has-uid
uid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-uid      | inj₂ _ = has-uid


tid[⇐] : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
tid[⇐] x∈dst has-tid-skip with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
... | opt₁ _ = has-tid
... | opt₂ _ = has-tid
... | opt₃ _ = has-tid-skip
tid[⇐] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid = has-tid
tid[⇐] {_} {event _ _ (lab-f RM)}    x∈dst has-tid = has-tid-skip
tid[⇐] {_} {event _ _ (lab-f WW)}    x∈dst has-tid with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
... | inj₁ _ = has-tid-skip
... | inj₂ _ = has-tid
tid[⇐] {_} {event _ _ (lab-f SC)}    x∈dst has-tid with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
... | inj₁ _ = has-tid-skip
... | inj₂ _ = has-tid

tid[$⇒] : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
tid[$⇒] {_} {event-skip _ _}          x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
tid[$⇒] {_} {event-skip _ _}          x∈dst has-tid      | opt₁ _ = has-tid-skip
tid[$⇒] {_} {event-skip _ _}          x∈dst has-tid      | opt₂ _ = has-tid-skip
tid[$⇒] {_} {event-skip _ _}          x∈dst has-tid-skip | opt₃ _ = has-tid-skip
tid[$⇒] {_} {event _ _ (lab-r _ _ _)} x∈dst has-tid      = has-tid
tid[$⇒] {_} {event _ _ (lab-w _ _ _)} x∈dst has-tid      = has-tid
tid[$⇒] {_} {event _ _ (lab-f RM)}    x∈dst has-tid-skip = has-tid
tid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
tid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-tid-skip | inj₁ _ = has-tid
tid[$⇒] {_} {event _ _ (lab-f WW)}    x∈dst has-tid      | inj₂ _ = has-tid
tid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
tid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-tid-skip | inj₁ _ = has-tid
tid[$⇒] {_} {event _ _ (lab-f SC)}    x∈dst has-tid      | inj₂ _ = has-tid


loc[⇐] : {loc : Location} → Pred[⇐]² (HasLoc loc)
loc[⇐] x∈dst has-loc-init = has-loc-init
loc[⇐] x∈dst (has-loc-r (is-r {tmov}) refl) with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
... | opt₁ _ = has-loc-r is-r refl
... | opt₂ _ = has-loc-r is-q refl
... | opt₃ _ = has-loc-r is-a refl
loc[⇐] x∈dst (has-loc-r (is-r {trmw}) refl) with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
... | inj₁ _ = has-loc-r is-r refl
... | inj₂ _ = has-loc-r is-a refl
loc[⇐] x∈dst (has-loc-w (is-w {tmov}) refl) with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
... | inj₁ _ = has-loc-w is-w refl
... | inj₂ _ = has-loc-w is-l refl
loc[⇐] x∈dst (has-loc-w (is-w {trmw}) refl) with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
... | inj₁ _ = has-loc-w is-w refl
... | inj₂ _ = has-loc-w is-l refl

loc[$⇒] : {loc : Location} → Pred[$⇒]² (HasLoc loc)
loc[$⇒] {_} {event-init _ _ _}           x∈dst has-loc-init = has-loc-init
loc[$⇒] {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
loc[$⇒] {_} {event-skip _ _}             x∈dst (has-loc-r () _) | opt₁ _
loc[$⇒] {_} {event-skip _ _}             x∈dst (has-loc-w () _) | opt₁ _
loc[$⇒] {_} {event-skip _ _}             x∈dst (has-loc-r () _) | opt₂ _
loc[$⇒] {_} {event-skip _ _}             x∈dst (has-loc-w () _) | opt₂ _
loc[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
loc[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (has-loc-r is-r refl) | opt₁ _ = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (has-loc-r is-q refl) | opt₂ _ = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (has-loc-r is-a refl) | opt₃ _ = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
loc[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (has-loc-r is-r refl) | inj₁ _ = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (has-loc-r is-a refl) | inj₂ _ = has-loc-r is-r refl
loc[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
loc[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (has-loc-w is-w refl) | inj₁ _ = has-loc-w is-w refl
loc[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (has-loc-w is-l refl) | inj₂ _ = has-loc-w is-w refl
loc[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
loc[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (has-loc-w is-w refl) | inj₁ _ = has-loc-w is-w refl
loc[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (has-loc-w is-l refl) | inj₂ _ = has-loc-w is-w refl
loc[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
loc[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst (has-loc-r () _) | inj₂ _
loc[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst (has-loc-w () _) | inj₂ _
loc[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
loc[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst (has-loc-r () _) | inj₂ _
loc[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst (has-loc-w () _) | inj₂ _


val[⇐] : {val : Value} → Pred[⇐]² (HasVal val)
val[⇐] x∈dst has-val-init = has-val-init
val[⇐] x∈dst (has-val-r (is-r {tmov}) refl) with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
... | opt₁ _ = has-val-r is-r refl
... | opt₂ _ = has-val-r is-q refl
... | opt₃ _ = has-val-r is-a refl
val[⇐] x∈dst (has-val-r (is-r {trmw}) refl) with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
... | inj₁ _ = has-val-r is-r refl
... | inj₂ _ = has-val-r is-a refl
val[⇐] x∈dst (has-val-w (is-w {tmov}) refl) with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
... | inj₁ _ = has-val-w is-w refl
... | inj₂ _ = has-val-w is-l refl
val[⇐] x∈dst (has-val-w (is-w {trmw}) refl) with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
... | inj₁ _ = has-val-w is-w refl
... | inj₂ _ = has-val-w is-l refl

val[$⇒] : {val : Value} → Pred[$⇒]² (HasVal val)
val[$⇒] {_} {event-init _ _ _}           x∈dst has-val-init = has-val-init
val[$⇒] {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
val[$⇒] {_} {event-skip _ _}             x∈dst (has-val-r () _) | opt₁ _
val[$⇒] {_} {event-skip _ _}             x∈dst (has-val-w () _) | opt₁ _
val[$⇒] {_} {event-skip _ _}             x∈dst (has-val-r () _) | opt₂ _
val[$⇒] {_} {event-skip _ _}             x∈dst (has-val-w () _) | opt₂ _
val[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
val[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (has-val-r is-r refl) | opt₁ _ = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (has-val-r is-q refl) | opt₂ _ = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (has-val-r is-a refl) | opt₃ _ = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
val[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (has-val-r is-r refl) | inj₁ _ = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (has-val-r is-a refl) | inj₂ _ = has-val-r is-r refl
val[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
val[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (has-val-w is-w refl) | inj₁ _ = has-val-w is-w refl
val[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (has-val-w is-l refl) | inj₂ _ = has-val-w is-w refl
val[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
val[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (has-val-w is-w refl) | inj₁ _ = has-val-w is-w refl
val[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (has-val-w is-l refl) | inj₂ _ = has-val-w is-w refl
val[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
val[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst (has-val-r () _) | inj₂ _
val[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst (has-val-w () _) | inj₂ _
val[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
val[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst (has-val-r () _) | inj₂ _
val[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst (has-val-w () _) | inj₂ _


Init[⇐] : Pred[⇐]² EvInit
Init[⇐] x∈dst ev-init = ev-init


Init[$⇒] : Pred[$⇒]² EvInit
Init[$⇒] {event-init _ _ _} x∈dst ev-init = ev-init
Init[$⇒] {event-skip _ _}   x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
Init[$⇒] {event-skip _ _}   x∈dst () | opt₁ _
Init[$⇒] {event-skip _ _}   x∈dst () | opt₂ _
Init[$⇒] {event-skip _ _}   x∈dst () | opt₃ _
Init[$⇒] {event _ _ (lab-f WW)} x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
Init[$⇒] {event _ _ (lab-f WW)} x∈dst () | inj₁ _
Init[$⇒] {event _ _ (lab-f WW)} x∈dst () | inj₂ _
Init[$⇒] {event _ _ (lab-f SC)} x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
Init[$⇒] {event _ _ (lab-f SC)} x∈dst () | inj₁ _
Init[$⇒] {event _ _ (lab-f SC)} x∈dst () | inj₂ _


Wₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvWₜ tag)
Wₜ[⇐]        x∈dst (ev-init refl)   = ev-init refl
Wₜ[⇐] {tmov} x∈dst (ev-w is-w refl) with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
... | inj₁ _ = ev-w is-w refl
... | inj₂ _ = ev-w is-l refl
Wₜ[⇐] {trmw} x∈dst (ev-w is-w refl) with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
... | inj₁ _ = ev-w is-w refl
... | inj₂ _ = ev-w is-l refl

Wₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvWₜ tag)
Wₜ[$⇒] {_} {event-init _ _ _} x∈dst (ev-init refl) = ev-init refl
Wₜ[$⇒] {_} {event-skip _ _} x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
Wₜ[$⇒] {_} {event-skip _ _} x∈dst (ev-w () _) | opt₁ _
Wₜ[$⇒] {_} {event-skip _ _} x∈dst (ev-w () _) | opt₂ _
Wₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-w _ refl) with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
Wₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-w () refl) | opt₁ _
Wₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-w () refl) | opt₂ _
Wₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-w () refl) | opt₃ _
Wₜ[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (ev-w _ refl) with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
Wₜ[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (ev-w () refl) | inj₁ _
Wₜ[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (ev-w () refl) | inj₂ _
Wₜ[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (ev-w _ refl) with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
Wₜ[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (ev-w is-w refl) | inj₁ _ = ev-w is-w refl
Wₜ[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (ev-w is-l refl) | inj₂ _ = ev-w is-w refl
Wₜ[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (ev-w _ refl) with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
Wₜ[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (ev-w is-w refl) | inj₁ _ = ev-w is-w refl
Wₜ[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (ev-w is-l refl) | inj₂ _ = ev-w is-w refl
Wₜ[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
Wₜ[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst (ev-w () _) | inj₂ _
Wₜ[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
Wₜ[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst (ev-w () _) | inj₂ _


Rₜ[⇐] : {tag : Tag} → Pred[⇐]² (EvRₜ tag)
Rₜ[⇐] {tmov} x∈dst (ev-r is-r refl) with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
... | opt₁ _ = ev-r is-r refl
... | opt₂ _ = ev-r is-q refl
... | opt₃ _ = ev-r is-a refl
Rₜ[⇐] {trmw} x∈dst (ev-r is-r refl) with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
... | inj₁ _ = ev-r is-r refl
... | inj₂ _ = ev-r is-a refl


Rₜ[$⇒] : {tag : Tag} → Pred[$⇒]² (EvRₜ tag)
Rₜ[$⇒] {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
Rₜ[$⇒] {_} {event-skip _ _}             x∈dst (ev-r () _) | opt₁ _
Rₜ[$⇒] {_} {event-skip _ _}             x∈dst (ev-r () _) | opt₂ _
Rₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-r _ refl) with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
Rₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-r is-r refl) | opt₁ _ = ev-r is-r refl
Rₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-r is-q refl) | opt₂ _ = ev-r is-r refl
Rₜ[$⇒] {_} {event _ _ (lab-r tmov _ _)} x∈dst (ev-r is-a refl) | opt₃ _ = ev-r is-r refl
Rₜ[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (ev-r _ refl) with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
Rₜ[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (ev-r is-r refl) | inj₁ _ = ev-r is-r refl
Rₜ[$⇒] {_} {event _ _ (lab-r trmw _ _)} x∈dst (ev-r is-a refl) | inj₂ _ = ev-r is-r refl
Rₜ[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (ev-r _ refl) with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
Rₜ[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (ev-r () refl) | inj₁ _
Rₜ[$⇒] {_} {event _ _ (lab-w tmov _ _)} x∈dst (ev-r () refl) | inj₂ _
Rₜ[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (ev-r _ refl) with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
Rₜ[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (ev-r () refl) | inj₁ _
Rₜ[$⇒] {_} {event _ _ (lab-w trmw _ _)} x∈dst (ev-r () refl) | inj₂ _
Rₜ[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
Rₜ[$⇒] {_} {event _ _ (lab-f WW)}       x∈dst (ev-r () _) | inj₂ _
Rₜ[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst x-r with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
Rₜ[$⇒] {_} {event _ _ (lab-f SC)}       x∈dst (ev-r () _) | inj₂ _


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

  --
  -- These mappings are mostly copy-pasted between them, and only differ slightly.
  --
  

  R₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (Armv8.EvR₌ tag loc val) (LIMM.EvR₌ tag loc val)
  R₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  R₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₁ _
  R₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₂ _
  R₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₃ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst ev-r₌ | opt₁ _ = ev-r₌
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst ev-r₌ | inj₁ _ = ev-r₌
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst () | inj₂ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst () | inj₂ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₁ _
  R₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₂ _
  
  R₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (Armv8.EvR₌ tag loc val) (LIMM.EvR₌ tag loc val)
  R₌[⇒] = [$⇒]→₁[⇒] R₌[$⇒]


  Q₌[$⇒] : {loc : Location} {val : Value}
    → Pred[$⇒] (Armv8.EvQ₌ loc val) (LIMM.EvR₌ tmov loc val)
  Q₌[$⇒] {_} {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  Q₌[$⇒] {_} {_} {event-skip _ _}             x∈dst () | opt₁ _
  Q₌[$⇒] {_} {_} {event-skip _ _}             x∈dst () | opt₂ _
  Q₌[$⇒] {_} {_} {event-skip _ _}             x∈dst () | opt₃ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  Q₌[$⇒] {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst ev-q₌ | opt₂ _ = ev-r₌
  Q₌[$⇒] {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  Q₌[$⇒] {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst () | inj₁ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst () | inj₂ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  Q₌[$⇒] {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst () | inj₂ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  Q₌[$⇒] {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst () | inj₁ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst () | inj₂ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  Q₌[$⇒] {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  Q₌[$⇒] {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₁ _
  Q₌[$⇒] {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₂ _
  
  Q₌[⇒] : {loc : Location} {val : Value}
    → Pred[⇒] (Armv8.EvQ₌ loc val) (LIMM.EvR₌ tmov loc val)
  Q₌[⇒] = [$⇒]→₁[⇒] Q₌[$⇒]


  A₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (Armv8.EvA₌ tag loc val) (LIMM.EvR₌ tag loc val)
  A₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  A₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₁ _
  A₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₂ _
  A₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₃ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst ev-a₌ | opt₃ _ = ev-r₌
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst ev-a₌ | inj₂ _ = ev-r₌
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst () | inj₂ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst () | inj₁ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst () | inj₂ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₁ _
  A₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₂ _


  A₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (Armv8.EvA₌ tag loc val) (LIMM.EvR₌ tag loc val)
  A₌[⇒] = [$⇒]→₁[⇒] A₌[$⇒]


  W₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (Armv8.EvW₌ tag loc val) (LIMM.EvW₌ tag loc val)
  W₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  W₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₁ _
  W₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₂ _
  W₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₃ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst () | opt₁ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst () | inj₁ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst ev-w₌ | inj₁ _ = ev-w₌
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst ev-w₌ | inj₁ _ = ev-w₌
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₁ _
  W₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₂ _
  
  W₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (Armv8.EvW₌ tag loc val) (LIMM.EvW₌ tag loc val)
  W₌[⇒] = [$⇒]→₁[⇒] W₌[$⇒]


  L₌[$⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[$⇒] (Armv8.EvL₌ tag loc val) (LIMM.EvW₌ tag loc val)
  L₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  L₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₁ _
  L₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₂ _
  L₌[$⇒] {_} {_} {_} {event-skip _ _}             x∈dst () | opt₃ _
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-r tmov _ _)} x∈dst () | opt₁ _
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-r trmw _ _)} x∈dst () | inj₁ _
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-w tmov _ _)} x∈dst ev-l₌ | inj₂ _ = ev-w₌
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-w trmw _ _)} x∈dst ev-l₌ | inj₂ _ = ev-w₌
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₁ _
  L₌[$⇒] {_} {_} {_} {event _ _ (lab-f SC)}       x∈dst () | inj₂ _
  
  L₌[⇒] : {tag : Tag} {loc : Location} {val : Value}
    → Pred[⇒] (Armv8.EvL₌ tag loc val) (LIMM.EvW₌ tag loc val)
  L₌[⇒] = [$⇒]→₁[⇒] L₌[$⇒]


  Fst[$⇒] : Pred[$⇒] (Armv8.EvF₌ F-st) (LIMM.EvF₌ WW)
  Fst[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  Fst[$⇒] {event-skip _ _}             x∈dst () | opt₁ _
  Fst[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Fst[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  Fst[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst () | opt₁ _
  Fst[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst () | opt₂ _
  Fst[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst () | opt₃ _
  Fst[$⇒] {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  Fst[$⇒] {event _ _ (lab-r trmw _ _)} x∈dst () | inj₁ _
  Fst[$⇒] {event _ _ (lab-r trmw _ _)} x∈dst () | inj₂ _
  Fst[$⇒] {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  Fst[$⇒] {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  Fst[$⇒] {event _ _ (lab-w tmov _ _)} x∈dst () | inj₂ _
  Fst[$⇒] {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  Fst[$⇒] {event _ _ (lab-w trmw _ _)} x∈dst () | inj₁ _
  Fst[$⇒] {event _ _ (lab-w trmw _ _)} x∈dst () | inj₂ _
  Fst[$⇒] {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  Fst[$⇒] {event _ _ (lab-f WW)}       x∈dst ()    | inj₁ _
  Fst[$⇒] {event _ _ (lab-f WW)}       x∈dst ev-f₌ | inj₂ _ = ev-f₌
  Fst[$⇒] {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  Fst[$⇒] {event _ _ (lab-f SC)}       x∈dst () | inj₁ _
  Fst[$⇒] {event _ _ (lab-f SC)}       x∈dst () | inj₂ _
  
  Fst[⇒] : Pred[⇒] (Armv8.EvF₌ F-st) (LIMM.EvF₌ WW)
  Fst[⇒] = [$⇒]→₁[⇒] Fst[$⇒]


  Ffull[$⇒] : Pred[$⇒] (Armv8.EvF₌ F-full) (LIMM.EvF₌ SC)
  Ffull[$⇒] {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  Ffull[$⇒] {event-skip _ _}             x∈dst () | opt₁ _
  Ffull[$⇒] {event-skip _ _}             x∈dst () | opt₂ _
  Ffull[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  Ffull[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst () | opt₁ _
  Ffull[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst () | opt₂ _
  Ffull[$⇒] {event _ _ (lab-r tmov _ _)} x∈dst () | opt₃ _
  Ffull[$⇒] {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  Ffull[$⇒] {event _ _ (lab-r trmw _ _)} x∈dst () | inj₁ _
  Ffull[$⇒] {event _ _ (lab-r trmw _ _)} x∈dst () | inj₂ _
  Ffull[$⇒] {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  Ffull[$⇒] {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  Ffull[$⇒] {event _ _ (lab-w tmov _ _)} x∈dst () | inj₂ _
  Ffull[$⇒] {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  Ffull[$⇒] {event _ _ (lab-w trmw _ _)} x∈dst () | inj₁ _
  Ffull[$⇒] {event _ _ (lab-w trmw _ _)} x∈dst () | inj₂ _
  Ffull[$⇒] {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  Ffull[$⇒] {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  Ffull[$⇒] {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  Ffull[$⇒] {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  Ffull[$⇒] {event _ _ (lab-f SC)}       x∈dst _ | inj₂ _ = ev-f₌

  Ffull[⇒] : Pred[⇒] (Armv8.EvF₌ F-full) (LIMM.EvF₌ SC)
  Ffull[⇒] = [$⇒]→₁[⇒] Ffull[$⇒]


  ISB[$⇒]skip : Pred[$⇒] Armv8.EvISB EvSkip
  ISB[$⇒]skip {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  ISB[$⇒]skip {event-skip _ _}             x∈dst ev-isb | opt₂ _ = ev-skip
  ISB[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  ISB[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst () | opt₁ _
  ISB[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst () | opt₂ _
  ISB[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst () | opt₃ _
  ISB[$⇒]skip {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  ISB[$⇒]skip {event _ _ (lab-r trmw _ _)} x∈dst () | inj₁ _
  ISB[$⇒]skip {event _ _ (lab-r trmw _ _)} x∈dst () | inj₂ _
  ISB[$⇒]skip {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  ISB[$⇒]skip {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  ISB[$⇒]skip {event _ _ (lab-w tmov _ _)} x∈dst () | inj₂ _
  ISB[$⇒]skip {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  ISB[$⇒]skip {event _ _ (lab-w trmw _ _)} x∈dst () | inj₁ _
  ISB[$⇒]skip {event _ _ (lab-w trmw _ _)} x∈dst () | inj₂ _
  ISB[$⇒]skip {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  ISB[$⇒]skip {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  ISB[$⇒]skip {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  ISB[$⇒]skip {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  ISB[$⇒]skip {event _ _ (lab-f SC)}       x∈dst () | inj₂ _

  ISB[⇒]skip : Pred[⇒] Armv8.EvISB EvSkip
  ISB[⇒]skip = [$⇒]→₁[⇒] ISB[$⇒]skip


  Fld[$⇒]skip : Pred[$⇒] (Armv8.EvF₌ F-ld) EvSkip
  Fld[$⇒]skip {event-skip _ _}             x∈dst _ with ⇔₁-apply-⊆₁ org-skip (x∈dst , ev-skip)
  Fld[$⇒]skip {event-skip _ _}             x∈dst ev-f₌ | opt₁ _ = ev-skip
  Fld[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rᵣ (x∈dst , ev-r is-r refl)
  Fld[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst () | opt₁ _
  Fld[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst () | opt₂ _
  Fld[$⇒]skip {event _ _ (lab-r tmov _ _)} x∈dst () | opt₃ _
  Fld[$⇒]skip {event _ _ (lab-r trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-rₐ (x∈dst , ev-r is-r refl)
  Fld[$⇒]skip {event _ _ (lab-r trmw _ _)} x∈dst () | inj₁ _
  Fld[$⇒]skip {event _ _ (lab-r trmw _ _)} x∈dst () | inj₂ _
  Fld[$⇒]skip {event _ _ (lab-w tmov _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  Fld[$⇒]skip {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  Fld[$⇒]skip {event _ _ (lab-w tmov _ _)} x∈dst () | inj₂ _
  Fld[$⇒]skip {event _ _ (lab-w trmw _ _)} x∈dst _ with ⇔₁-apply-⊆₁ org-wₐ (x∈dst , ev-w is-w refl)
  Fld[$⇒]skip {event _ _ (lab-w trmw _ _)} x∈dst () | inj₁ _
  Fld[$⇒]skip {event _ _ (lab-w trmw _ _)} x∈dst () | inj₂ _
  Fld[$⇒]skip {event _ _ (lab-f WW)}       x∈dst _ with ⇔₁-apply-⊆₁ org-ww (x∈dst , ev-f₌)
  Fld[$⇒]skip {event _ _ (lab-f WW)}       x∈dst () | inj₁ _
  Fld[$⇒]skip {event _ _ (lab-f WW)}       x∈dst () | inj₂ _
  Fld[$⇒]skip {event _ _ (lab-f SC)}       x∈dst _ with ⇔₁-apply-⊆₁ org-sc (x∈dst , ev-f₌)
  Fld[$⇒]skip {event _ _ (lab-f SC)}       x∈dst () | inj₂ _

  Fld[⇒]skip : Pred[⇒] (Armv8.EvF₌ F-ld) EvSkip
  Fld[⇒]skip = [$⇒]→₁[⇒] Fld[$⇒]skip
  

  -- | The origin of an Lᵣ (non-RMW release write) in the target is always a Wᵣ in the source.
  l-org : {xᵗ : Event LabelLIMM} → (x∈dst : xᵗ ∈ events dst) → EvLₜ tmov (ev[⇐] x∈dst) → org-wᵣ-l xᵗ
  l-org {event _ _ (lab-w tmov _ _)} x∈dst x-lᵣ with ⇔₁-apply-⊆₁ org-wᵣ (x∈dst , ev-w is-w refl)
  l-org {event _ _ (lab-w tmov _ _)} x∈dst () | inj₁ _
  l-org {event _ _ (lab-w tmov _ _)} x∈dst _  | inj₂ org = org
  l-org {event _ _ (lab-w trmw _ _)} x∈dst x-lᵣ = ⊥-elim (disjoint-wₜ _ (lₜ⇒wₜ x-lᵣ , Wₜ[⇐] x∈dst (ev-w is-w refl)))
  -- impossible cases
  l-org {event-skip _ _}          x∈dst x-lᵣ = ⊥-elim (disjoint-w/skip _ (W[⇒] (events[⇐] x∈dst) (wₜ⇒w (lₜ⇒wₜ x-lᵣ)) , ev-skip))
  l-org {event _ _ (lab-r _ _ _)} x∈dst x-lᵣ = ⊥-elim (disjoint-r/w _ (ev-r is-r , W[⇒] (events[⇐] x∈dst) (wₜ⇒w (lₜ⇒wₜ x-lᵣ))))
  l-org {event _ _ (lab-f _)}     x∈dst x-lᵣ = ⊥-elim (disjoint-f/w _ (ev-f is-f , W[⇒] (events[⇐] x∈dst) (wₜ⇒w (lₜ⇒wₜ x-lᵣ))))
