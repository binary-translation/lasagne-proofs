{-# OPTIONS --safe #-}

-- | Properties and operations for events.
module Arch.General.Properties where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃-syntax; _,_; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Helpers
open import Arch.General.Event


-- | File Structure:
--
-- > General
-- > Operations
--   > Substitution
--     > Predicates
--     > `Same` structures
--   > Coercion
--     > Labels
--     > Sets
--   > Set splits
--   > Tag inequality
-- > Properties
--   > Uniqueness
--     > Values
--     > Proofs
--   > Symmetry
--   > Transitivity
--   > Set Relations
--   > Disjoint Sets


open LabelClass {{...}}


-- # General

-- | Every event has a unique identifier
ev-uid : ∀ {Label : Set} {{_ : LabelClass Label}} → (ev : Event Label) → UniqueId
ev-uid (event-init uid _ _) = uid
ev-uid (event-skip uid _)   = uid
ev-uid (event uid _ _)      = uid

-- | Every event has a witness of its Unique ID
ev-has-uid : ∀ {Label : Set} {{_ : LabelClass Label}} → (ev : Event Label) → HasUid (ev-uid ev) ev
ev-has-uid (event-init _ _ _) = has-uid-init
ev-has-uid (event-skip _ _)   = has-uid-skip
ev-has-uid (event _ _ _)      = has-uid

has-uid-dec : ∀ {Label : Set} {{_ : LabelClass Label}} → (uid : UniqueId) → DecPred (HasUid uid)
has-uid-dec uid x with ℕ-dec (ev-uid x) uid
... | yes refl = yes (ev-has-uid x)
... | no  ¬uid = no lemma
  where
  lemma : ¬ HasUid uid x
  lemma has-uid-init = ¬uid refl
  lemma has-uid-skip = ¬uid refl
  lemma has-uid      = ¬uid refl

-- | Every /skip/ event has a Thread ID
skip-tid : ∀ {Label : Set} {{_ : LabelClass Label}} → {ev : Event Label} → EvSkip ev → ThreadId
skip-tid {ev = event-skip _ tid} ev-skip = tid

-- | Every /skip/ event has a witness of its Thread ID
skip-has-tid : ∀ {Label : Set} {{_ : LabelClass Label}} → {ev : Event Label} → (ev-skip : EvSkip ev) → HasTid (skip-tid ev-skip) ev
skip-has-tid ev-skip = has-tid-skip

-- | Every event is either a init event, or it has a Thread ID
ev-init/tid : ∀ {Label : Set} {{_ : LabelClass Label}} → XOptPred₂ EvInit HasSomeTid
ev-init/tid (event-init _ _ _) = xopt₁ ev-init (λ())
ev-init/tid (event-skip _ tid) = xopt₂ (λ()) (tid , has-tid-skip)
ev-init/tid (event _ tid _)    = xopt₂ (λ()) (tid , has-tid)

disjoint-init/tid : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {tid : ThreadId}
  → Disjoint₁ EvInit (HasTid tid)
disjoint-init/tid _ (ev-init , ())


-- ## Operations: Set splits

r/tag : {Label : Set} {{_ : LabelClass Label}} {x : Event Label} → EvR x → (EvRₜ tmov ∪₁ EvRₜ trmw) x
r/tag (ev-r lab-r) with inspect (lab-r-tag lab-r)
... | tmov with≡ tag≡tmov = inj₁ (ev-r lab-r (≡-sym tag≡tmov))
... | trmw with≡ tag≡trmw = inj₂ (ev-r lab-r (≡-sym tag≡trmw))

w/tag : {Label : Set} {{_ : LabelClass Label}} {x : Event Label} → EvW x → (EvWₜ tmov ∪₁ EvWₜ trmw) x
w/tag ev-init = inj₁ (ev-init refl)
w/tag (ev-w lab-w) with inspect (lab-w-tag lab-w)
... | tmov with≡ tag≡tmov = inj₁ (ev-w lab-w (≡-sym tag≡tmov))
... | trmw with≡ tag≡trmw = inj₂ (ev-w lab-w (≡-sym tag≡trmw))

wᵣ/init : {Label : Set} {{_ : LabelClass Label}} {x : Event Label} → EvWᵣ x → (EvInit ∪₁ EvWₙₜ tmov) x
wᵣ/init (ev-init refl)        = inj₁ ev-init
wᵣ/init (ev-w lab-w tmov≡tag) = inj₂ (ev-w lab-w tmov≡tag)

rw/rw : {Label : Set} {{_ : LabelClass Label}} {x : Event Label} → EvRW x → (EvR ∪₁ EvW) x
rw/rw ev-init      = inj₂ ev-init
rw/rw (ev-r lab-r) = inj₁ (ev-r lab-r)
rw/rw (ev-w lab-w) = inj₂ (ev-w lab-w)

rwₜ/rw : {Label : Set} {{_ : LabelClass Label}} {x : Event Label} {tag : Tag} → EvRWₜ tag x → (EvRₜ tag ∪₁ EvWₜ tag) x
rwₜ/rw (ev-init refl)    = inj₂ (ev-init refl)
rwₜ/rw (ev-r lab-r refl) = inj₁ (ev-r lab-r refl)
rwₜ/rw (ev-w lab-w refl) = inj₂ (ev-w lab-w refl)

rwₙₜ/rw : {Label : Set} {{_ : LabelClass Label}} {x : Event Label} {tag : Tag} → EvRWₙₜ tag x → (EvRₜ tag ∪₁ EvWₙₜ tag) x
rwₙₜ/rw (ev-r lab-r refl) = inj₁ (ev-r lab-r refl)
rwₙₜ/rw (ev-w lab-w refl) = inj₂ (ev-w lab-w refl)

rw/tag : {Label : Set} {{_ : LabelClass Label}} {x : Event Label} → EvRW x → (EvRWₜ tmov ∪₁ EvRWₜ trmw) x
rw/tag ev-init = inj₁ (ev-init refl)
rw/tag (ev-r lab-r) with inspect (lab-r-tag lab-r)
... | tmov with≡ tag≡tmov = inj₁ (ev-r lab-r (≡-sym tag≡tmov))
... | trmw with≡ tag≡trmw = inj₂ (ev-r lab-r (≡-sym tag≡trmw))
rw/tag (ev-w lab-w) with inspect (lab-w-tag lab-w)
... | tmov with≡ tag≡tmov = inj₁ (ev-w lab-w (≡-sym tag≡tmov))
... | trmw with≡ tag≡trmw = inj₂ (ev-w lab-w (≡-sym tag≡trmw))



-- | Every read event has a location
r-loc : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvR ev → Location
r-loc (ev-r lab-r) = lab-r-loc lab-r

-- | Every read event has a witness of its location
r-has-loc : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-r : EvR ev) → HasLoc (r-loc ev-r) ev
r-has-loc (ev-r lab-r) = has-loc-r lab-r refl

-- | Every read event has a value
r-val : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvR ev → Value
r-val (ev-r lab-r) = lab-r-val lab-r

-- | Every read event has a witness of its value
r-has-val : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-r : EvR ev) → HasVal (r-val ev-r) ev
r-has-val (ev-r lab-r) = has-val-r lab-r refl

-- | Every read event has a tag
r-tag : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-r : EvR ev) → Tag
r-tag (ev-r lab-r) = lab-r-tag lab-r

-- | Every write event has a location
w-loc : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvW ev → Location
w-loc {ev = event-init _ loc _} ev-init = loc
w-loc (ev-w lab-w) = lab-w-loc lab-w

-- | Every write event has a witness of its location
w-has-loc : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-w : EvW ev) → HasLoc (w-loc ev-w) ev
w-has-loc ev-init      = has-loc-init
w-has-loc (ev-w lab-w) = has-loc-w lab-w refl

-- | Every write event has a value
w-val : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvW ev → Value
w-val {ev = event-init _ _ val} ev-init = val
w-val (ev-w lab-w) = lab-w-val lab-w

-- | Every write event has a witness of its location
w-has-val : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-w : EvW ev) → HasVal (w-val ev-w) ev
w-has-val ev-init      = has-val-init
w-has-val (ev-w lab-w) = has-val-w lab-w refl

-- | Every write event has a tag
w-tag : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvW ev → Tag
w-tag ev-init      = tmov
w-tag (ev-w lab-w) = lab-w-tag lab-w

¬f-loc : {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvF ev → ¬ (∃[ loc ] HasLoc loc ev)
¬f-loc (ev-f lab-f) (loc , has-loc-r lab-r refl) = xopt₃-select₁₃ lab-r lab-f (labs-xopt _)
¬f-loc (ev-f lab-f) (loc , has-loc-w lab-w refl) = xopt₃-select₂₃ lab-w lab-f (labs-xopt _)

¬f-val : {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvF ev → ¬ (∃[ val ] HasVal val ev)
¬f-val (ev-f lab-f) (val , has-val-r lab-r refl) = xopt₃-select₁₃ lab-r lab-f (labs-xopt _)
¬f-val (ev-f lab-f) (val , has-val-w lab-w refl) = xopt₃-select₂₃ lab-w lab-f (labs-xopt _)

¬skip-loc : {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvSkip ev → ¬ (∃[ loc ] HasLoc loc ev)
¬skip-loc ev-skip (loc , ())

¬skip-val : {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvSkip ev → ¬ (∃[ val ] HasVal val ev)
¬skip-val ev-skip (val , ())

rw-tag : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-rw : EvRW ev) → Tag
rw-tag x-rw with rw/rw x-rw
... | inj₁ x-r = r-tag x-r
... | inj₂ x-w = w-tag x-w

-- | Every init event has a location
init-loc : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvInit ev → Location
init-loc {ev = event-init _ loc _} ev-init = loc

-- | Every init event has a location
init-has-loc : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-init : EvInit ev) → HasLoc (init-loc ev-init) ev
init-has-loc ev-init = has-loc-init

-- | Every init event has a value
init-val : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvInit ev → Value
init-val {ev = event-init _ _ val} ev-init = val

-- | Every init event has a location
init-has-val : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-init : EvInit ev) → HasVal (init-val ev-init) ev
init-has-val ev-init = has-val-init

-- | Every event is in the set of events (E).
ev-e : ∀ {Label : Set} {{_ : LabelClass Label}} (ev : Event Label) → EvE ev
ev-e (event-init _ _ _) = ev-init
ev-e (event-skip _ _)   = ev-skip
ev-e (event _ _ lab)    = xopt₃-apply ev-r ev-w ev-f (labs-xopt lab)


-- # Operations

-- ## Operations: Substitution

-- ### Operations - Subsititution: Predicates

subst-uid : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {u₁ u₂ : UniqueId}
  → u₁ ≡ u₂
  → HasUid u₁ ev
    ------------
  → HasUid u₂ ev
subst-uid refl has-uid-init = has-uid-init
subst-uid refl has-uid-skip = has-uid-skip
subst-uid refl has-uid      = has-uid

subst-tid : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {t₁ t₂ : ThreadId}
  → t₁ ≡ t₂
  → HasTid t₁ ev
    ------------
  → HasTid t₂ ev
subst-tid refl has-tid-skip = has-tid-skip
subst-tid refl has-tid      = has-tid

subst-loc : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {l₁ l₂ : Location}
  → l₁ ≡ l₂
  → HasLoc l₁ ev
    ------------
  → HasLoc l₂ ev
subst-loc refl has-loc-init           = has-loc-init
subst-loc refl (has-loc-r lab-r refl) = has-loc-r lab-r refl
subst-loc refl (has-loc-w lab-w refl) = has-loc-w lab-w refl

subst-val : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {v₁ v₂ : Value}
  → v₁ ≡ v₂
  → HasVal v₁ ev
    ------------
  → HasVal v₂ ev
subst-val refl has-val-init           = has-val-init
subst-val refl (has-val-r lab-r refl) = has-val-r lab-r refl
subst-val refl (has-val-w lab-w refl) = has-val-w lab-w refl


-- ### Operations - Subsititution: `Same` structures

subst-suid : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {x y : Event Label}
  → SameUid x y
  → {uid : UniqueId}
  → HasUid uid x
    -------------------
  → HasUid uid y
subst-suid (same-uid has-uid-init x-uid) has-uid-init = x-uid
subst-suid (same-uid has-uid-skip x-uid) has-uid-skip = x-uid
subst-suid (same-uid has-uid x-uid)      has-uid      = x-uid

subst-stid : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {x y : Event Label}
  → SameTid x y
  → {tid : ThreadId}
  → HasTid tid x
    -------------------
  → HasTid tid y
subst-stid (same-tid has-tid-skip x-tid) has-tid-skip = x-tid
subst-stid (same-tid has-tid x-tid)      has-tid      = x-tid

subst-sloc : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {x y : Event Label}
  → SameLoc x y
  → {loc : Location}
  → HasLoc loc x
    -------------------
  → HasLoc loc y
subst-sloc (same-loc has-loc-init x-loc) has-loc-init = x-loc
subst-sloc (same-loc (has-loc-r lab-r₁ refl) x-loc) (has-loc-r lab-r₂ refl) with labs-r-unique _ lab-r₁ lab-r₂
... | refl = x-loc
subst-sloc (same-loc (has-loc-w lab-w₁ refl) x-loc) (has-loc-w lab-w₂ refl) with labs-w-unique _ lab-w₁ lab-w₂
... | refl = x-loc
subst-sloc (same-loc (has-loc-r lab-r refl) _) (has-loc-w lab-w _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))
subst-sloc (same-loc (has-loc-w lab-w refl) _) (has-loc-r lab-r _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))

subst-sval : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {x y : Event Label}
  → SameVal x y
  → {val : Value}
  → HasVal val x
    -------------------
  → HasVal val y
subst-sval (same-val has-val-init x-val) has-val-init = x-val
subst-sval (same-val (has-val-r lab-r₁ refl) x-val) (has-val-r lab-r₂ refl) with labs-r-unique _ lab-r₁ lab-r₂
... | refl = x-val
subst-sval (same-val (has-val-w lab-w₁ refl) x-val) (has-val-w lab-w₂ refl) with labs-w-unique _ lab-w₁ lab-w₂
... | refl = x-val
subst-sval (same-val (has-val-r lab-r refl) _) (has-val-w lab-w _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))
subst-sval (same-val (has-val-w lab-w refl) _) (has-val-r lab-r _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))


-- ## Operations: Coercion

-- ### Operations - Coercion: Labels

coerce-init-label : ∀ {Label₁ Label₂ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}}
  → {uid₁ uid₂ : UniqueId} {loc₁ loc₂ : Location} → {val₁ val₂ : Value}
  → event-init {Label₁} uid₁ loc₁ val₁ ≡ event-init {Label₁} uid₂ loc₂ val₂
  → event-init {Label₂} uid₁ loc₁ val₁ ≡ event-init {Label₂} uid₂ loc₂ val₂
coerce-init-label refl = refl

coerce-skip-label : ∀ {Label₁ Label₂ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}}
  → {uid₁ uid₂ : UniqueId} {tid₁ tid₂ : ThreadId}
  → event-skip {Label₁} uid₁ tid₁ ≡ event-skip {Label₁} uid₂ tid₂
  → event-skip {Label₂} uid₁ tid₁ ≡ event-skip {Label₂} uid₂ tid₂
coerce-skip-label refl = refl


-- ### Operations - Coercion: Sets

r⇒rₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-r : EvR ev) → EvRₜ (r-tag ev-r) ev
r⇒rₜ (ev-r lab-r) = ev-r lab-r refl

rₜ⇒r : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvRₜ tag ev → EvR ev
rₜ⇒r (ev-r lab-r refl) = ev-r lab-r

r⇒rw : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvR ev → EvRW ev
r⇒rw (ev-r x-r) = ev-r x-r

rₜ⇒rwₙₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvRₜ tag ev → EvRWₙₜ tag ev
rₜ⇒rwₙₜ (ev-r lab-r refl) = ev-r lab-r refl

rₜ⇒rwₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvRₜ tag ev → EvRWₜ tag ev
rₜ⇒rwₜ (ev-r lab-r refl) = ev-r lab-r refl

rₜ⇒rw : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvRₜ tag ev → EvRW ev
rₜ⇒rw = r⇒rw ∘ rₜ⇒r

w⇒wₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → (ev-w : EvW ev) → EvWₜ (w-tag ev-w) ev
w⇒wₜ ev-init      = ev-init refl
w⇒wₜ (ev-w lab-w) = ev-w lab-w refl

wₜ⇒w : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvWₜ tag ev → EvW ev
wₜ⇒w (ev-init refl)    = ev-init
wₜ⇒w (ev-w lab-w refl) = ev-w lab-w

w⇒rw : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvW ev → EvRW ev
w⇒rw ev-init    = ev-init
w⇒rw (ev-w x-w) = ev-w x-w

wₜ⇒rwₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvWₜ tag ev → EvRWₜ tag ev
wₜ⇒rwₜ (ev-init refl)    = ev-init refl
wₜ⇒rwₜ (ev-w lab-w refl) = ev-w lab-w refl

wₙₜ⇒rwₙₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag}
  → EvWₙₜ tag ev → EvRWₙₜ tag ev
wₙₜ⇒rwₙₜ (ev-w lab-w refl) = ev-w lab-w refl

wₜ⇒rw : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvWₜ tag ev → EvRW ev
wₜ⇒rw = w⇒rw ∘ wₜ⇒w

wₙₜ⇒wₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvWₙₜ tag ev → EvWₜ tag ev
wₙₜ⇒wₜ (ev-w lab-w refl) = ev-w lab-w refl

wₙₜ⇒w : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvWₙₜ tag ev → EvW ev
wₙₜ⇒w = wₜ⇒w ∘ wₙₜ⇒wₜ

wₙₜ⇒wₙ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag} → EvWₙₜ tag ev → EvWₙ ev
wₙₜ⇒wₙ (ev-w lab-w refl) = ev-w lab-w

rwₜ⇒rw : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} {tag : Tag}
  → EvRWₜ tag ev → EvRW ev
rwₜ⇒rw (ev-init refl)    = ev-init
rwₜ⇒rw (ev-w lab-w refl) = ev-w lab-w
rwₜ⇒rw (ev-r lab-r refl) = ev-r lab-r

rw⇒rwₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label}
  → (ev-rw : EvRW ev) → EvRWₜ (rw-tag ev-rw) ev
rw⇒rwₜ ev-init      = ev-init refl
rw⇒rwₜ (ev-w lab-w) = ev-w lab-w refl
rw⇒rwₜ (ev-r lab-r) = ev-r lab-r refl

rwₙₜ⇒rwₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label}
  → {tag : Tag} → (ev-rw : EvRWₙₜ tag ev) → EvRWₜ tag ev
rwₙₜ⇒rwₜ (ev-w lab-w refl) = ev-w lab-w refl
rwₙₜ⇒rwₜ (ev-r lab-r refl) = ev-r lab-r refl

init⇒wₜ : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvInit ev → EvWₜ tmov ev
init⇒wₜ ev-init = ev-init refl

f⇒e : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvF ev → EvE ev
f⇒e (ev-f x-f) = ev-f x-f

rw⇒e : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvRW ev → EvE ev
rw⇒e ev-init    = ev-init
rw⇒e (ev-r x-r) = ev-r x-r
rw⇒e (ev-w x-w) = ev-w x-w

r⇒e : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvR ev → EvE ev
r⇒e = rw⇒e ∘ r⇒rw

w⇒e : ∀ {Label : Set} {{_ : LabelClass Label}} {ev : Event Label} → EvW ev → EvE ev
w⇒e = rw⇒e ∘ w⇒rw


-- ## Operations: Tag inequality

mov≢rmw : tmov ≢ trmw
mov≢rmw ()


-- # Properties

-- ## Properties: Uniqueness

-- ### Properties - Uniqueness: Values

-- | The UID of an event is unique.
--
-- That is, every event has at most one UID.
uid-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {ev : Event Label} → Unique₁ _≡_ (λ uid → HasUid uid ev)
uid-unique has-uid-init has-uid-init = refl
uid-unique has-uid-skip has-uid-skip = refl
uid-unique has-uid      has-uid      = refl

-- | The Thread ID of an event is unique.
--
-- That is, every event has at most one Thread ID.
tid-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {ev : Event Label} → Unique₁ _≡_ (λ tid → HasTid tid ev)
tid-unique has-tid      has-tid      = refl
tid-unique has-tid-skip has-tid-skip = refl

-- | The location of an event is unique.
--
-- That is, every event has at most one location.
loc-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {ev : Event Label} → Unique₁ _≡_ (λ loc → HasLoc loc ev)
loc-unique has-loc-init            has-loc-init            = refl
loc-unique (has-loc-r lab-r₁ refl) (has-loc-r lab-r₂ refl) = cong lab-r-loc (labs-r-unique _ lab-r₁ lab-r₂)
loc-unique (has-loc-w lab-w₁ refl) (has-loc-w lab-w₂ refl) = cong lab-w-loc (labs-w-unique _ lab-w₁ lab-w₂)
loc-unique (has-loc-r lab-r refl)  (has-loc-w lab-w refl)  = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))
loc-unique (has-loc-w lab-w refl)  (has-loc-r lab-r refl)  = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))

-- | The value of an event is unique.
--
-- That is, every event has at most one value.
val-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {ev : Event Label} → Unique₁ _≡_ (λ val → HasVal val ev)
val-unique has-val-init    has-val-init    = refl
val-unique (has-val-r lab-r₁ refl) (has-val-r lab-r₂ refl) = cong lab-r-val (labs-r-unique _ lab-r₁ lab-r₂)
val-unique (has-val-w lab-w₁ refl) (has-val-w lab-w₂ refl) = cong lab-w-val (labs-w-unique _ lab-w₁ lab-w₂)
val-unique (has-val-r lab-r refl)  (has-val-w lab-w refl)  = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))
val-unique (has-val-w lab-w refl)  (has-val-r lab-r refl)  = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))


-- ### Properties - Uniqueness: Proofs

-- | The proof that an event has a particular UID is unique.
has-uid-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {uid : UniqueId} → UniquePred (HasUid uid)
has-uid-unique _ has-uid-init has-uid-init = refl
has-uid-unique _ has-uid-skip has-uid-skip = refl
has-uid-unique _ has-uid      has-uid      = refl

-- | The proof that an event has a particular Thread ID is unique.
has-tid-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {tid : ThreadId} → UniquePred (HasTid tid)
has-tid-unique _ has-tid-skip has-tid-skip = refl
has-tid-unique _ has-tid      has-tid      = refl

has-loc-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {loc : Location} → UniquePred (HasLoc loc)
has-loc-unique _ has-loc-init has-loc-init = refl
has-loc-unique _ (has-loc-r lab-r₁ _)    (has-loc-r lab-r₂ _) with labs-r-unique _ lab-r₁ lab-r₂
has-loc-unique _ (has-loc-r lab-r₁ refl) (has-loc-r lab-r₂ refl) | refl = refl
has-loc-unique _ (has-loc-w lab-w₁ _)    (has-loc-w lab-w₂ _) with labs-w-unique _ lab-w₁ lab-w₂
has-loc-unique _ (has-loc-w lab-w₁ refl) (has-loc-w lab-w₂ refl) | refl = refl
-- Impossible cases
has-loc-unique _ (has-loc-r lab-r _)     (has-loc-w lab-w _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))
has-loc-unique _ (has-loc-w lab-w _)     (has-loc-r lab-r _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))

has-val-unique : ∀ {Label : Set} {{_ : LabelClass Label}}
  → {val : Value} → UniquePred (HasVal val)
has-val-unique _ has-val-init has-val-init = refl
has-val-unique _ (has-val-r lab-r₁ _)    (has-val-r lab-r₂ _) with labs-r-unique _ lab-r₁ lab-r₂
has-val-unique _ (has-val-r lab-r₁ refl) (has-val-r lab-r₂ refl) | refl = refl
has-val-unique _ (has-val-w lab-w₁ _)    (has-val-w lab-w₂ _) with labs-w-unique _ lab-w₁ lab-w₂
has-val-unique _ (has-val-w lab-w₁ refl) (has-val-w lab-w₂ refl) | refl = refl
-- Impossible cases
has-val-unique _ (has-val-r lab-r _)     (has-val-w lab-w _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))
has-val-unique _ (has-val-w lab-w _)     (has-val-r lab-r _) = ⊥-elim (xopt₃-select₁₂ lab-r lab-w (labs-xopt _))

w-unique : ∀ {Label : Set} {{_ : LabelClass Label}} → UniquePred EvW
w-unique _ ev-init ev-init = refl
w-unique _ (ev-w lab-w₁) (ev-w lab-w₂) with labs-w-unique _ lab-w₁ lab-w₂
w-unique _ (ev-w lab-w₁) (ev-w lab-w₂) | refl = refl

r-unique : ∀ {Label : Set} {{_ : LabelClass Label}} → UniquePred EvR
r-unique _ (ev-r lab-r₁) (ev-r lab-r₂) with labs-r-unique _ lab-r₁ lab-r₂
r-unique _ (ev-r lab-r₁) (ev-r lab-r₂) | refl = refl

f-unique : ∀ {Label : Set} {{_ : LabelClass Label}} → UniquePred EvF
f-unique _ (ev-f lab-f₁) (ev-f lab-f₂) with labs-f-unique _ lab-f₁ lab-f₂
f-unique _ (ev-f lab-f₁) (ev-f lab-f₂) | refl = refl

init-unique : ∀ {Label : Set} {{_ : LabelClass Label}} → UniquePred EvInit
init-unique _ ev-init ev-init = refl

skip-unique : ∀ {Label : Set} {{_ : LabelClass Label}} → UniquePred EvSkip
skip-unique _ ev-skip ev-skip = refl


-- ## Properties: Excluded Middle

stid-dec : ∀ {Label : Set} {{_ : LabelClass Label}} → DecRel (SameTid {Label})
stid-dec x y with ev-init/tid x | ev-init/tid y
stid-dec .(event-init _ _ _) y | xopt₁ ev-init _ | _ = no λ{(same-tid () _)}
stid-dec x y | xopt₂ _ x-tid | xopt₁ ev-init _ = no λ{(same-tid _ ())}
stid-dec x y | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) with ℕ-dec tid₁ tid₂
stid-dec x y | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (.tid₁ , y-tid₁) | yes refl = yes (same-tid x-tid₁ y-tid₁)
stid-dec x y | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂)  | no tid₁≢tid₂ =
  no (λ{xy-stid → tid₁≢tid₂ (tid-unique (subst-stid xy-stid x-tid₁) y-tid₂)})


tag-eq-dec : DecRel (_≡_ {_} {Tag})
tag-eq-dec tmov tmov = yes refl
tag-eq-dec trmw trmw = yes refl
tag-eq-dec tmov trmw = no (λ ())
tag-eq-dec trmw tmov = no (λ ())


ev-eq-dec : {Label : Set} {{_ : LabelClass Label}}
  → DecRel (_≡_ {_} {Event Label})
ev-eq-dec (event-init uid₁ loc₁ val₁) (event-init uid₂ loc₂ val₂) =
  cong₃-dec event-init (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (ℕ-dec uid₁ uid₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
ev-eq-dec (event-skip uid₁ tid₁) (event-skip uid₂ tid₂) =
  cong₂-dec event-skip (λ{refl → refl}) (λ{refl → refl}) (ℕ-dec uid₁ uid₂) (ℕ-dec tid₁ tid₂)
ev-eq-dec (event uid₁ tid₁ lab₁) (event uid₂ tid₂ lab₂) =
  cong₃-dec event (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (ℕ-dec uid₁ uid₂) (ℕ-dec tid₁ tid₂) (lab-eq-dec lab₁ lab₂)
-- Unequal cases
ev-eq-dec (event-init _ _ _) (event-skip _ _)   = no (λ())
ev-eq-dec (event-init _ _ _) (event _ _ _)      = no (λ())
ev-eq-dec (event-skip _ _)   (event-init _ _ _) = no (λ())
ev-eq-dec (event-skip _ _)   (event _ _ _)      = no (λ())
ev-eq-dec (event _ _ _)      (event-init _ _ _) = no (λ())
ev-eq-dec (event _ _ _)      (event-skip _ _)   = no (λ())
  

-- ## Properties: Symmetry

-- Note that the default definitions of `Symmetric` and `Transitivity` are /not/ used; This is because
-- the properties below need to work across different labels, which those default definitions disallow.

sym-same-uid : ∀ {Label₁ Label₂ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}}
  → {x : Event Label₁} {y : Event Label₂}
  → SameUid x y
    -----------
  → SameUid y x
sym-same-uid (same-uid x y) = same-uid y x

sym-same-tid : ∀ {Label₁ Label₂ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}}
  → {x : Event Label₁} {y : Event Label₂}
  → SameTid x y
    -----------
  → SameTid y x
sym-same-tid (same-tid x y) = same-tid y x

sym-same-loc : ∀ {Label₁ Label₂ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}}
  → {x : Event Label₁} {y : Event Label₂}
  → SameLoc x y
    -----------
  → SameLoc y x
sym-same-loc (same-loc x y) = same-loc y x

sym-same-val : ∀ {Label₁ Label₂ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}}
  → {x : Event Label₁} {y : Event Label₂}
  → SameVal x y
    -----------
  → SameVal y x
sym-same-val (same-val x y) = same-val y x


-- ## Properties: Transitivity

-- Transitivity of `SameLoc`
trans-same-loc : ∀ {Label₁ Label₂ Label₃ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}} {{_ : LabelClass Label₃}}
  → Trans (SameLoc {Label₁} {Label₂}) (SameLoc {Label₂} {Label₃}) (SameLoc {Label₁} {Label₃})
trans-same-loc (same-loc x y₁) (same-loc y₂ z) = 
  same-loc x (subst-loc (≡-sym (loc-unique y₁ y₂)) z)
  
-- Two-step transitivity of `SameLoc`
trans-same-loc₂ : ∀ {Label₁ Label₂ Label₃ Label₄ : Set}
    {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}} {{_ : LabelClass Label₃}} {{_ : LabelClass Label₄}}
  → Trans₂ (SameLoc {Label₁} {Label₂}) (SameLoc {Label₂} {Label₃}) (SameLoc {Label₃} {Label₄}) (SameLoc {Label₁} {Label₄})
trans-same-loc₂ x~y y~z z~w = trans-same-loc x~y (trans-same-loc y~z z~w)


-- Transitivity of `SameVal`
trans-same-val : ∀ {Label₁ Label₂ Label₃ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}} {{_ : LabelClass Label₃}}
  → Trans (SameVal {Label₁} {Label₂}) (SameVal {Label₂} {Label₃}) (SameVal {Label₁} {Label₃})
trans-same-val (same-val x y₁) (same-val y₂ z) =
  same-val x (subst-val (≡-sym (val-unique y₁ y₂)) z)
  
-- Two-step transitivity of `SameVal`
trans-same-val₂ : ∀ {Label₁ Label₂ Label₃ Label₄ : Set}
    {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}} {{_ : LabelClass Label₃}} {{_ : LabelClass Label₄}}
  → Trans₂ (SameVal {Label₁} {Label₂}) (SameVal {Label₂} {Label₃}) (SameVal {Label₃} {Label₄}) (SameVal {Label₁} {Label₄})
trans-same-val₂ x~y y~z z~w = trans-same-val x~y (trans-same-val y~z z~w)


-- Transitivity of `SameTid`
trans-same-tid : ∀ {Label₁ Label₂ Label₃ : Set} {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}} {{_ : LabelClass Label₃}}
  → Trans (SameTid {Label₁} {Label₂}) (SameTid {Label₂} {Label₃}) (SameTid {Label₁} {Label₃})
trans-same-tid (same-tid x y₁) (same-tid y₂ z) =
  same-tid x (subst-tid (≡-sym (tid-unique y₁ y₂)) z)
  
-- Two-step transitivity of `SameTid`
trans-same-tid₂ : ∀ {Label₁ Label₂ Label₃ Label₄ : Set}
    {{_ : LabelClass Label₁}} {{_ : LabelClass Label₂}} {{_ : LabelClass Label₃}} {{_ : LabelClass Label₄}}
  → Trans₂ (SameTid {Label₁} {Label₂}) (SameTid {Label₂} {Label₃}) (SameTid {Label₃} {Label₄}) (SameTid {Label₁} {Label₄})
trans-same-tid₂ x~y y~z z~w = trans-same-tid x~y (trans-same-tid y~z z~w)


-- ## Properties: Set Relations

Init⊆W : ∀ {Label : Set} {{_ : LabelClass Label}} → EvInit {Label} ⊆₁ EvW {Label}
Init⊆W = ⊆: λ{_ ev-init → ev-init}

R⊆RW : ∀ {Label : Set} {{_ : LabelClass Label}} → EvR {Label} ⊆₁ EvRW {Label}
R⊆RW = ⊆: λ{_ → r⇒rw}

W⊆RW : ∀ {Label : Set} {{_ : LabelClass Label}} → EvW {Label} ⊆₁ EvRW {Label}
W⊆RW = ⊆: λ{_ → w⇒rw}

R⊆E : ∀ {Label : Set} {{_ : LabelClass Label}} → EvR {Label} ⊆₁ EvE {Label}
R⊆E = ⊆: λ{_ (ev-r is-lab-r) → ev-r is-lab-r}

W⊆E : ∀ {Label : Set} {{_ : LabelClass Label}} → EvW {Label} ⊆₁ EvE {Label}
W⊆E = ⊆: λ{_ ev-init → ev-init; _ (ev-w is-lab-w) → ev-w is-lab-w}

F⊆E : ∀ {Label : Set} {{_ : LabelClass Label}} → EvF {Label} ⊆₁ EvE {Label}
F⊆E = ⊆: λ{_ (ev-f is-lab-f) → ev-f is-lab-f}

W⊆SomeLoc : ∀ {Label : Set} {{_ : LabelClass Label}} → EvW ⊆₁ HasSomeLoc
W⊆SomeLoc = ⊆: (λ{_ → < w-loc , w-has-loc >})

R⊆SomeLoc : ∀ {Label : Set} {{_ : LabelClass Label}} → EvR ⊆₁ HasSomeLoc
R⊆SomeLoc = ⊆: (λ{_ → < r-loc , r-has-loc >})

W⊆SomeVal : ∀ {Label : Set} {{_ : LabelClass Label}} → EvW ⊆₁ HasSomeVal
W⊆SomeVal = ⊆: (λ{_ → < w-val , w-has-val >})

R⊆SomeVal : ∀ {Label : Set} {{_ : LabelClass Label}} → EvR ⊆₁ HasSomeVal
R⊆SomeVal = ⊆: (λ{_ → < r-val , r-has-val >})


-- ## Properties: Disjoint Sets

disjoint-r/w : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvR EvW
disjoint-r/w _ (ev-r lab-r , ev-w lab-w) = xopt₃-select₁₂ lab-r lab-w (labs-xopt _)

disjoint-f/r : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvF EvR
disjoint-f/r _ (ev-f lab-f , ev-r lab-r) = xopt₃-select₁₃ lab-r lab-f (labs-xopt _)

disjoint-f/w : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvF EvW
disjoint-f/w _ (ev-f lab-f , ev-w lab-w) = xopt₃-select₂₃ lab-w lab-f (labs-xopt _)

disjoint-f/rw : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvF EvRW
disjoint-f/rw _ (x-f , x-rw) with rw/rw x-rw
... | inj₁ x-r = disjoint-f/r _ (x-f , x-r)
... | inj₂ x-w = disjoint-f/w _ (x-f , x-w)

disjoint-r/init : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvR EvInit
disjoint-r/init _ (ev-r lab-r , ())

disjoint-wₜ/init : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ (EvWₜ trmw) EvInit
disjoint-wₜ/init _ (ev-init () , ev-init)

disjoint-wₙ/init : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvWₙ EvInit
disjoint-wₙ/init _ (() , ev-init)

disjoint-f/init : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvF EvInit
disjoint-f/init _ (() , ev-init)

disjoint-skip/init : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvSkip EvInit
disjoint-skip/init _ (ev-skip , ())

disjoint-r/skip : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvR EvSkip
disjoint-r/skip _ (() , ev-skip)

disjoint-w/skip : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvW EvSkip
disjoint-w/skip _ (() , ev-skip)

disjoint-f/skip : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvF EvSkip
disjoint-f/skip _ (() , ev-skip)

disjoint-init/rwₙₜ : ∀ {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ EvInit (EvRWₙₜ tmov)
disjoint-init/rwₙₜ _ (ev-init , ())

disjoint-wₜ : {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ (EvWₜ tmov) (EvWₜ trmw)
disjoint-wₜ _ (ev-init refl , ev-init ())
disjoint-wₜ _ (ev-w lab-w₁ tmov≡tag₁ , ev-w lab-w₂ trmw≡tag₂)
  with labs-w-unique _ lab-w₁ lab-w₂
... | refl = mov≢rmw (≡-trans tmov≡tag₁ (≡-sym trmw≡tag₂))

disjoint-rₜ : {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ (EvRₜ tmov) (EvRₜ trmw)
disjoint-rₜ _ (ev-r lab-r₁ tmov≡tag₁ , ev-r lab-r₂ trmw≡tag₂)
  with labs-r-unique _ lab-r₁ lab-r₂
... | refl = mov≢rmw (≡-trans tmov≡tag₁ (≡-sym trmw≡tag₂))

disjoint-rwₜ : {Label : Set} {{_ : LabelClass Label}} → Disjoint₁ (EvRWₜ tmov) (EvRWₜ trmw)
disjoint-rwₜ x (x-mov , x-rmw) with rwₜ/rw x-mov | rwₜ/rw x-rmw
... | inj₁ x-r-mov | inj₁ x-r-rmw = disjoint-rₜ x (x-r-mov , x-r-rmw)
... | inj₁ x-r-mov | inj₂ x-w-rmw = disjoint-r/w x (rₜ⇒r x-r-mov , wₜ⇒w x-w-rmw)
... | inj₂ x-w-mov | inj₁ x-r-rmw = disjoint-r/w x (rₜ⇒r x-r-rmw , wₜ⇒w x-w-mov)
... | inj₂ x-w-mov | inj₂ x-w-rmw = disjoint-wₜ x (x-w-mov , x-w-rmw)
