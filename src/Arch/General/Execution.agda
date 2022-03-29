{-# OPTIONS --safe #-}

module Arch.General.Execution where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; subst; subst₂) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero; suc to ℓsuc)
open import Function using (_∘_)
open import Data.Nat using (zero)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (IsStrictTotalOrder)
open import Relation.Binary renaming (IsStrictTotalOrder to STO)
open import Function using (flip)
-- Local library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Arch.General.Event
open import Arch.General.Properties


-- # Definitions

-- ## Definitions: Execution

record Execution (Label : Set) {{_ : LabelClass Label}} : Set₁ where
  field
    -- # Events
    
    events : Pred (Event Label) ℓzero


    -- # Relations between events
    
    -- ## Primitive relations

    -- | Program order
    po : Rel (Event Label) ℓzero -- E×E
    -- | Reads-from
    rf : Rel (Event Label) ℓzero -- W×R
    -- | Coherence order
    co : Rel (Event Label) ℓzero -- W×W


    -- ## Derived relations

    -- | Read-modify-write
    rmw : Rel (Event Label) ℓzero -- R×W

open Execution


-- ## Definitions: Execution Relation Helpers

--
-- + Design Decision: internal/external
--
-- There are multiple ways of defining internal/external relations.
-- An alternative way (to the one below) is defining:
--
-- internal r ex = r ex ∩₂ (po ex ∪₂ flip (po ex))
--
-- Then, whenever `r x y` holds, either `po x y` or `po y x` must
-- In case, po-related concerns either direction.
--
-- In our definition below, we consider only the `po x y` case.
-- In practice, `po y x` is statically eliminated through the
-- coherence property enforced by many architectures.
--
--
-- Yet another definition may /seem possible/:
--
-- internal r ex = r ex ∩₂ SameTid
--
-- That one, however, is /not/ possible, as init events don't have
-- thread IDs. Init events should be internally-related to
-- subsequent events, as the occur along the `po` before the
-- "real execution" starts.
--
-- That could be solved by defining:
--
-- internal r ex = r ex ∩₂ (SameTid ∪₂ (EvInit ×₂ EvE))
-- external r ex = r ex ∩₂ (¬₂ (SameTid ∪₂ (EvInit ×₂ EvE)))
-- 
-- That - arguably - becomes a too-complicated definition.
--


internal : {Label : Set} {{_ : LabelClass Label}}
  → (Execution Label → Rel (Event Label) ℓzero)
  → (ex : Execution Label)
    -------------------------------------------
  → Rel (Event Label) ℓzero
internal R ex = R ex ∩₂ po ex

external : {Label : Set} {{_ : LabelClass Label}}
  → (Execution Label → Rel (Event Label) ℓzero)
  → (ex : Execution Label)
    -------------------------------------------
  → Rel (Event Label) ℓzero
external R ex = R ex ∩₂ (¬₂ po ex)

internal⊆ : {Label : Set} {{_ : LabelClass Label}}
  → (R : Execution Label → Rel (Event Label) ℓzero)
  → (ex : Execution Label)
    -----------------------------------------------
  → internal R ex ⊆₂ R ex
internal⊆ R ex = ∩₂-introʳ-⊆₂

external⊆ : {Label : Set} {{_ : LabelClass Label}}
  → (R : Execution Label → Rel (Event Label) ℓzero)
  → (ex : Execution Label)
    -----------------------------------------------
  → external R ex ⊆₂ R ex
external⊆ R ex = ∩₂-introʳ-⊆₂


-- # Definitions: Derived Execution Relations

-- | From-read derived relation (R×W)
fr : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
fr ex = flip (rf ex) ⨾ (co ex)

-- | Same-location events along the program order
po-loc : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
po-loc ex = po ex ∩₂ SameLoc

po-imm : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
po-imm ex = immediate (po ex)

-- | External read-from relation
rfe : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
rfe = external rf

-- | Internal read-from relation
rfi : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
rfi = internal rf

-- | External coherence-order relation
coe : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
coe = external co

-- | Internal coherence-order relation
coi : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
coi = internal co

-- | External from-read relation
fre : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
fre = external fr

-- | Internal from-read relation
fri : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    -----------------------
  → Rel (Event Label) ℓzero
fri = internal fr


-- # Definitions: Well-formedness

-- | Wellformedness declares that an execution "makes sense".
--
-- For instance, it guarantees every Read event reads-from exactly one Write event,
-- `po` and `co` are actually /orders/, and initialization events happen at the beginning,
-- and so on.
--
-- Note that Wellformedness is a /general/ property that holds for any execution
-- (in the axiomatic model) regardless of the architecture-specifics.
-- Architecture-specific constraints should be included in an Architecture's /consistency/
-- specification.
record WellFormed {Label : Set} {{_ : LabelClass Label}} (ex : Execution Label) : Set₁ where
  field
    -- # General constraints

    -- | Event UIDs are unique.
    -- That is, for every UID there exists (at most) one event in the execution.
    unique-ids : ∀ (uid : UniqueId) → Unique₁ _≡_ (HasUid uid ∩₁ events ex)

    -- | Event membership is unique.
    -- That is, there is only one way of stating that an event `x` is in the execution.
    events-unique : UniquePred (events ex)
    
    rmw-def  : rmw ex ⊆₂ po-imm ex
    rmw-w    : codom (rmw ex) ⇔₁ ( events ex ∩₁ EvWₜ trmw )

    rf-w×r  : rf ex  ⊆₂ ( EvW ×₂ EvR )
    co-w×w  : co ex  ⊆₂ ( EvW ×₂ EvW )
    rmw-r×w : rmw ex ⊆₂ EvRₜ trmw ×₂ EvWₜ trmw

    po-init-first : ⊤-Precedes-⊥ EvInit (po ex) -- init events before non-init events
    co-init-first : ⊤-Precedes-⊥ EvInit (co ex) -- init events before non-init events
    
    -- Note that 'po' and 'co' are /strict/ orders (i.e., irreflexive).
    -- If they were non-strict they'd always be cyclic.
    
    -- `po` is /total/ over same-thread events, and init events, which don't have a thread ID
    po-tri : ∀ (tid : ThreadId) → Trichotomous _≡_ (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events ex) (po ex))
    -- between any two non-immediate po-related events, there exists another event
    po-splittable : SplittableOrder (po ex)
    
    -- `co` is /total/ over same-location Write events
    co-tri : ∀ (loc : Location) → Trichotomous _≡_ (filter-rel (EvW ∩₁ HasLoc loc ∩₁ events ex) (co ex))
    co-trans : Transitive (co ex)

    -- For every unique ID, either there is an event with that ID, or there is not
    events-uid-dec : (uid : UniqueId) → Dec (∃[ x ] (HasUid uid ∩₁ events ex) x)
    -- Every event either /is/ in the domain of `rmw` or it /is not/.
    rmwˡ-dec : DecPred (dom (rmw ex))
    
    po-elements : udr (po ex) ⇔₁ events ex
    rf-elements : udr (rf ex) ⊆₁ events ex
    co-elements : udr (co ex) ⊆₁ events ex

    po-stid  : po ex  ⊆₂ ((EvInit ×₂ EvE) ∪₂ SameTid)
    rf-sloc  : rf ex  ⊆₂ SameLoc
    co-sloc  : co ex  ⊆₂ SameLoc
    rmw-sloc : rmw ex ⊆₂ SameLoc
    rf-sval  : rf ex  ⊆₂ SameVal

    -- ## Well formed
    -- Every read-event reads from a preceding write. That is, every read event
    -- shows up in the co-domain of `rf`.
    wf-rf-≥1 : (EvR ∩₁ events ex) ⊆₁ codom (rf ex)
    -- Every read-event reads from *at most* one write
    wf-rf-≤1 : Functional _≡_ (flip (rf ex)) -- at most once
    
    -- All memory locations are initialized
    wf-init-≥1 : ∀ (loc : Location) → NonEmpty₁ (EvInit ∩₁ HasLoc loc ∩₁ events ex) -- at least once
    wf-init-≤1 : ∀ (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ events ex) -- at most once

open WellFormed


-- ## Well-formedness Properties

-- | The behavior of an execution is defined as the value at each memory location,
-- upon program termination.
behavior : {Label : Set} {{_ : LabelClass Label}}
  → Execution Label
    ------------------------
  → REL Location Value ℓzero
behavior ex loc val =
  ∃[ ev ] (ev ∈ events ex × EvW ev × HasVal val ev × HasLoc loc ev × maximal (co ex) ev)
