{-# OPTIONS --safe #-}

module Arch.Armv8 where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl) renaming (sym to ≡-sym)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty; _∈_)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties using (tag-eq-dec; ev-eq-dec)
open import Arch.General.Execution
open import Arch.General.DerivedWellformed


open Event
open Execution


--
-- # Notes on model
--
-- RMW creates R and W events
-- RMW_A creates A and W events
-- RMW_L creates A and L events
--


data F-mode : Set where
  F-full : F-mode
  F-ld   : F-mode
  F-st   : F-mode


data LabelArmv8 : Set where
  lab-r : Tag → Location → Value → LabelArmv8
  lab-a : Tag → Location → Value → LabelArmv8 -- ^ acquire read
  lab-q : Location → Value → LabelArmv8 -- ^ acquirePC read (always tmov)
  
  lab-w : Tag → Location → Value → LabelArmv8 -- ^ write
  lab-l : Tag → Location → Value → LabelArmv8 -- ^ release write

  lab-f   : F-mode → LabelArmv8 -- ^ fence
  lab-isb : LabelArmv8 -- ^ ISB (control) fence


data LabR : LabelArmv8 → Set where
  is-r : ∀ {tag : Tag} {loc : Location} {val : Value} → LabR (lab-r tag loc val)
  is-a : ∀ {tag : Tag} {loc : Location} {val : Value} → LabR (lab-a tag loc val)
  is-q : ∀ {loc : Location} {val : Value} → LabR (lab-q loc val)


data LabW : LabelArmv8 → Set where
  is-w : ∀ {tag : Tag} {loc : Location} {val : Value} → LabW (lab-w tag loc val)
  is-l : ∀ {tag : Tag} {loc : Location} {val : Value} → LabW (lab-l tag loc val)


data LabF : LabelArmv8 → Set where
  is-f   : ∀ {mode : F-mode} → LabF (lab-f mode)
  is-isb : LabF lab-isb



-- # Lemmas/Properties

private

  labs-xopt : XOptPred₃ LabR LabW LabF
  labs-xopt (lab-r _ _ _) = xopt₁ is-r  (λ()) (λ())
  labs-xopt (lab-a _ _ _) = xopt₁ is-a  (λ()) (λ())
  labs-xopt (lab-q _ _)   = xopt₁ is-q  (λ()) (λ())
  labs-xopt (lab-w _ _ _) = xopt₂ (λ()) is-w  (λ())
  labs-xopt (lab-l _ _ _) = xopt₂ (λ()) is-l  (λ())
  labs-xopt (lab-f _)     = xopt₃ (λ()) (λ()) is-f
  labs-xopt lab-isb       = xopt₃ (λ()) (λ()) is-isb


  r-unique : UniquePred LabR
  r-unique _ is-r is-r = refl
  r-unique _ is-a is-a = refl
  r-unique _ is-q is-q = refl


  w-unique : UniquePred LabW
  w-unique _ is-w is-w = refl
  w-unique _ is-l is-l = refl


  f-unique : UniquePred LabF
  f-unique _ is-f   is-f   = refl
  f-unique _ is-isb is-isb = refl


  r-tag : {lab : LabelArmv8} → LabR lab → Tag
  r-tag {lab-r tag _ _} is-r = tag
  r-tag {lab-a tag _ _} is-a = tag
  r-tag {lab-q _ _}     is-q = tmov


  w-tag : {lab : LabelArmv8} → LabW lab → Tag
  w-tag {lab-w tag _ _} is-w = tag
  w-tag {lab-l tag _ _} is-l = tag


  r-loc : {lab : LabelArmv8} → LabR lab → Location
  r-loc {lab-r _ loc _} is-r = loc
  r-loc {lab-a _ loc _} is-a = loc
  r-loc {lab-q loc _}   is-q = loc


  r-val : {lab : LabelArmv8} → LabR lab → Value
  r-val {lab-r _ _ val} is-r = val
  r-val {lab-a _ _ val} is-a = val
  r-val {lab-q _ val}   is-q = val


  w-loc : {lab : LabelArmv8} → LabW lab → Location
  w-loc {lab-w _ loc _} is-w = loc
  w-loc {lab-l _ loc _} is-l = loc


  w-val : {lab : LabelArmv8} → LabW lab → Value
  w-val {lab-w _ _ val} is-w = val
  w-val {lab-l _ _ val} is-l = val


  fence-dec : DecRel (_≡_ {_} {F-mode})
  fence-dec F-full F-full = yes refl
  fence-dec F-ld   F-ld   = yes refl
  fence-dec F-st   F-st   = yes refl
  -- false cases
  fence-dec F-full F-ld   = no (λ ())
  fence-dec F-full F-st   = no (λ())
  fence-dec F-ld   F-full = no (λ())
  fence-dec F-ld   F-st   = no (λ())
  fence-dec F-st   F-full = no (λ())
  fence-dec F-st   F-ld   = no (λ())


  lab-eq-dec : DecRel (_≡_ {_} {LabelArmv8})
  lab-eq-dec (lab-r tag₁ loc₁ val₁) (lab-r tag₂ loc₂ val₂) =
    cong₃-dec lab-r
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-a tag₁ loc₁ val₁) (lab-a tag₂ loc₂ val₂) =
    cong₃-dec lab-a
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-q loc₁ val₁) (lab-q loc₂ val₂) =
    cong₂-dec lab-q
      (λ{refl → refl}) (λ{refl → refl})
      (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-w tag₁ loc₁ val₁) (lab-w tag₂ loc₂ val₂) =
    cong₃-dec lab-w
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-l tag₁ loc₁ val₁) (lab-l tag₂ loc₂ val₂) =
    cong₃-dec lab-l
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-f m₁) (lab-f m₂) = cong-dec lab-f (λ{refl → refl}) (fence-dec m₁ m₂)
  lab-eq-dec lab-isb lab-isb = yes refl
  -- false cases
  lab-eq-dec (lab-r _ _ _) (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-r _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-r _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-a _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-a _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-q _ _)   (lab-f _)     = no (λ())
  lab-eq-dec (lab-q _ _)   lab-isb       = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-w _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-l _ _ _) (lab-f _)     = no (λ())
  lab-eq-dec (lab-l _ _ _) lab-isb       = no (λ())
  lab-eq-dec (lab-f _)     (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     (lab-a _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     (lab-q _ _)   = no (λ())
  lab-eq-dec (lab-f _)     (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     (lab-l _ _ _) = no (λ())
  lab-eq-dec (lab-f _)     lab-isb       = no (λ())
  lab-eq-dec lab-isb       (lab-r _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-a _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-q _ _)   = no (λ())
  lab-eq-dec lab-isb       (lab-w _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-l _ _ _) = no (λ())
  lab-eq-dec lab-isb       (lab-f _)     = no (λ())


instance
  LabelArmv8-ok : LabelClass LabelArmv8
  LabelArmv8-ok =
    record
      { labs-r        = LabR
      ; labs-w        = LabW
      ; labs-f        = LabF
      ; labs-xopt     = labs-xopt
      ; labs-r-unique = r-unique
      ; labs-w-unique = w-unique
      ; labs-f-unique = f-unique
      ; lab-r-tag     = r-tag
      ; lab-w-tag     = w-tag
      ; lab-r-loc     = r-loc
      ; lab-r-val     = r-val
      ; lab-w-loc     = w-loc
      ; lab-w-val     = w-val
      ; lab-eq-dec    = lab-eq-dec
      }


-- release write
data EvL : Event LabelArmv8 → Set where
  ev-l : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → EvL (event uid tid (lab-l tag loc val))


-- acquire read
data EvA : Event LabelArmv8 → Set where
  ev-a : {uid : UniqueId} {tid : ThreadId} {tag : Tag} {loc : Location} {val : Value} → EvA (event uid tid (lab-a tag loc val))


-- release write indexed by tag
data EvLₜ (tag : Tag) : Event LabelArmv8 → Set where
  ev-l : {uid : UniqueId} {tid : ThreadId} {loc : Location} {val : Value} → EvLₜ tag (event uid tid (lab-l tag loc val))


-- acquire read indexed by tag
data EvAₜ (tag : Tag) : Event LabelArmv8 → Set where
  ev-a : {uid : UniqueId} {tid : ThreadId} {loc : Location} {val : Value} → EvAₜ tag (event uid tid (lab-a tag loc val))


-- acquirePC read
data EvQ : Event LabelArmv8 → Set where
  ev-q : {uid : UniqueId} {tid : ThreadId} {loc : Location} {val : Value} → EvQ (event uid tid (lab-q loc val))


data EvISB : Event LabelArmv8 → Set where
  ev-isb : {uid : UniqueId} {tid : ThreadId} → EvISB (event uid tid lab-isb)
  
data EvA₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-a₌ : {uid : UniqueId} {tid : ThreadId} → EvA₌ tag loc val (event uid tid (lab-a tag loc val))


data EvQ₌ (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-q₌ : {uid : UniqueId} {tid : ThreadId} → EvQ₌ loc val (event uid tid (lab-q loc val))


data EvL₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-l₌ : {uid : UniqueId} {tid : ThreadId} → EvL₌ tag loc val (event uid tid (lab-l tag loc val))


data EvR₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-r₌ : {uid : UniqueId} {tid : ThreadId} → EvR₌ tag loc val (event uid tid (lab-r tag loc val))


data EvW₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelArmv8 → Set where
  ev-w₌ : {uid : UniqueId} {tid : ThreadId} → EvW₌ tag loc val (event uid tid (lab-w tag loc val))


data EvF₌ (mode : F-mode) : Event LabelArmv8 → Set where
  ev-f₌ : {uid : UniqueId} {tid : ThreadId} → EvF₌ mode (event uid tid (lab-f mode))


record Armv8Execution (ex : Execution LabelArmv8) : Set₁ where
  field
    -- # Armv8-specific relations
    
    data₋ : Rel (Event LabelArmv8) ℓzero -- called `data₋`, because `data` is a keyword
    addr  : Rel (Event LabelArmv8) ℓzero
    ctrl  : Rel (Event LabelArmv8) ℓzero
    
    -- # Armv8-specific relations

    data-def₁ : data₋ ⊆₂ EvR ×₂ EvW
    data-def₂ : data₋ ⊆₂ po ex
    addr-def₁ : addr  ⊆₂ EvR ×₂ ( EvR ∪₁ EvW )
    addr-def₂ : addr  ⊆₂ po ex
    ctrl-def₁ : ctrl  ⊆₂ EvR ×₂ EvE
    ctrl-def₂ : ctrl  ⊆₂ po ex
    ctrl-def₃ : ctrl ⨾ po ex ⊆₂ ctrl

open Armv8Execution


-- Barrier-ordered-before
--
-- Consider this the union over all relations in it's constructors.
--
-- This data structure is much easier to handle than taking _∪₂_ over all,
-- as constructing (or pattern-matching on) an instance looks like: inj₁ (inj₁ (inj₁ ...)))
data Bob (ex : Execution LabelArmv8) (x y : Event LabelArmv8) : Set where
  bob-f   : ( po ex ⨾ ⦗ EvF₌ F-full ⦘ ⨾ po ex )                   x y → Bob ex x y
  bob-la  : ( ⦗ EvL ⦘ ⨾ po ex ⨾ ⦗ EvA ⦘ )                         x y → Bob ex x y
  bob-fld : ( ⦗ EvR ⦘ ⨾ po ex ⨾ ⦗ EvF₌ F-ld ⦘ ⨾ po ex )           x y → Bob ex x y
  bob-acq : ( ⦗ EvA ∪₁ EvQ ⦘ ⨾ po ex )                            x y → Bob ex x y
  bob-fst : ( ⦗ EvW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ F-st ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ ) x y → Bob ex x y
  bob-l₁  : ( po ex ⨾ ⦗ EvL ⦘ )                                   x y → Bob ex x y
  bob-l₂  : ( po ex ⨾ ⦗ EvL ⦘ ⨾ coi ex )                          x y → Bob ex x y


-- Observed by
data Obs (ex : Execution LabelArmv8) (x y : Event LabelArmv8) : Set where
  obs-rfe : rfe ex x y → Obs ex x y
  obs-coe : coe ex x y → Obs ex x y
  obs-fre : fre ex x y → Obs ex x y


-- Data ordered before
data Dob {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) (x y : Event LabelArmv8) : Set where
  dob-addr    : addr a8                                                              x y → Dob a8 x y
  dob-data    : data₋ a8                                                             x y → Dob a8 x y
  dob-ctrl    : ( ctrl a8 ⨾ ⦗ EvW ⦘ )                                                x y → Dob a8 x y
  dob-isb     : ( ( ctrl a8 ∪₂ ( addr a8 ⨾ po ex ) ) ⨾ ⦗ EvISB ⦘ ⨾ po ex ⨾ ⦗ EvR ⦘ ) x y → Dob a8 x y
  dob-addr-po : ( addr a8 ⨾ po ex ⨾ ⦗ EvW ⦘ )                                        x y → Dob a8 x y
  dob-coi     : ( ( ctrl a8 ∪₂ data₋ a8 ) ⨾ coi ex )                                 x y → Dob a8 x y
  dob-rfi     : ( ( addr a8 ∪₂ data₋ a8 ) ⨾ rfi ex )                                 x y → Dob a8 x y


-- Atomic ordered before
data Aob (ex : Execution LabelArmv8) (x y : Event LabelArmv8) : Set where
  aob-rmw : rmw ex                                           x y → Aob ex x y
  aob-rfi : ( ⦗ codom (rmw ex) ⦘ ⨾ rfi ex ⨾ ⦗ EvA ∪₁ EvQ ⦘ ) x y → Aob ex x y


-- Immediate Ordered Before. (`Ob` is its transitive closure)
data Obi {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) (x y : Event LabelArmv8) : Set where
  obi-init : ( ⦗ EvInit ⦘ ⨾ po ex ) x y → Obi a8 x y
  obi-obs  : Obs ex                 x y → Obi a8 x y
  obi-dob  : Dob a8                 x y → Obi a8 x y
  obi-aob  : Aob ex                 x y → Obi a8 x y
  obi-bob  : Bob ex                 x y → Obi a8 x y


-- Ordered Before
Ob : {ex : Execution LabelArmv8} (a8 : Armv8Execution ex) → Rel (Event LabelArmv8) ℓzero
Ob a8 = TransClosure (Obi a8)


record IsArmv8Consistent (ex : Execution LabelArmv8) : Set₁ where
  field
    a8 : Armv8Execution ex

    -- # Armv8-specific consistency constraints
    
    ax-coherence  : Acyclic _≡_ ( po-loc ex ∪₂ rf ex ∪₂ fr ex ∪₂ co ex )
    ax-atomicity  : Empty₂ ( rmw ex ∩₂ (fre ex ⨾ coe ex) )
    ax-global-obs : Irreflexive _≡_ (Ob a8)

open IsArmv8Consistent



-- # Helpers

open import Arch.General.Properties
open WellFormed


l⇒w : {x : Event LabelArmv8} → EvL x → EvW x
l⇒w ev-l = ev-w is-l

lₜ⇒wₜ : {tag : Tag} {x : Event LabelArmv8} → EvLₜ tag x → EvWₜ tag x
lₜ⇒wₜ ev-l = ev-w is-l refl

a⇒r : {x : Event LabelArmv8} → EvA x → EvR x
a⇒r ev-a = ev-r is-a

q⇒r : {x : Event LabelArmv8} → EvQ x → EvR x
q⇒r ev-q = ev-r is-q

aₜ⇒rₜ : {tag : Tag} {x : Event LabelArmv8} → EvAₜ tag x → EvRₜ tag x
aₜ⇒rₜ ev-a = ev-r is-a refl

r₌⇒rₜ : {tag : Tag} {x : Location} {v : Value} {a : Event LabelArmv8} → EvR₌ tag x v a → EvRₜ tag a
r₌⇒rₜ ev-r₌ = ev-r is-r refl
  
q₌⇒rₜ : {x : Location} {v : Value} {a : Event LabelArmv8} → EvQ₌ x v a → EvRₜ tmov a
q₌⇒rₜ ev-q₌ = ev-r is-q refl

a₌⇒rₜ : {tag : Tag} {x : Location} {v : Value} {a : Event LabelArmv8} → EvA₌ tag x v a → EvRₜ tag a
a₌⇒rₜ ev-a₌ = ev-r is-a refl

l₌⇒lₜ : {tag : Tag} {x : Location} {v : Value} {a : Event LabelArmv8} → EvL₌ tag x v a → EvLₜ tag a
l₌⇒lₜ ev-l₌ = ev-l

f₌⇒f : {x : Event LabelArmv8} {mode : F-mode} → EvF₌ mode x → EvF x
f₌⇒f ev-f₌ = ev-f is-f


l/tag : {x : Event LabelArmv8} → EvL x → (EvLₜ tmov ∪₁ EvLₜ trmw) x
l/tag {event _ _ (lab-l tmov _ _)} ev-l = inj₁ ev-l
l/tag {event _ _ (lab-l trmw _ _)} ev-l = inj₂ ev-l


a/tag : {x : Event LabelArmv8} → EvA x → (EvAₜ tmov ∪₁ EvAₜ trmw) x
a/tag {event _ _ (lab-a tmov _ _)} ev-a = inj₁ ev-a
a/tag {event _ _ (lab-a trmw _ _)} ev-a = inj₂ ev-a


disjoint-init/l : Disjoint₁ EvInit EvL
disjoint-init/l _ (() , ev-l)


bob⇒po : {ex : Execution LabelArmv8}
  → WellFormed ex
  → {x y : Event LabelArmv8}
  → Bob ex x y
    ----------
  → po ex x y
bob⇒po wf (bob-f (po[xz] ⨾[ _ ]⨾ (refl , z-f) ⨾[ _ ]⨾ po[zy])) =
  po-trans wf po[xz] po[zy]
bob⇒po wf (bob-la ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) = po[xy]
bob⇒po wf (bob-fld ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy])) =
  po-trans wf po[xz] po[zy]
bob⇒po wf (bob-acq ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
bob⇒po wf (bob-fst ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _))) =
  po-trans wf po[xz] po[zy]
bob⇒po wf (bob-l₁ (po[xy] ⨾[ _ ]⨾ (refl , _))) = po[xy]
bob⇒po wf (bob-l₂ (po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ coi[zy])) =
  po-trans wf po[xz] (proj₂ coi[zy])


dob⇒po : {ex : Execution LabelArmv8}
  → WellFormed ex
  → (a8 : Armv8Execution ex)
  → {x y : Event LabelArmv8}
  → Dob a8 x y
    ----------
  → po ex x y
dob⇒po wf a8 (dob-addr addr[xy]) = ⊆₂-apply (addr-def₂ a8) addr[xy]
dob⇒po wf a8 (dob-data data[xy]) = ⊆₂-apply (data-def₂ a8) data[xy]
dob⇒po wf a8 (dob-ctrl (ctrl[xy] ⨾[ _ ]⨾ (refl , _))) = ⊆₂-apply (ctrl-def₂ a8) ctrl[xy]
dob⇒po wf a8 (dob-isb (inj₁ ctrl[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _))) =
  po-trans wf (⊆₂-apply (ctrl-def₂ a8) ctrl[xz]) po[zy]
dob⇒po wf a8 (dob-isb (inj₂ (addr[xv] ⨾[ _ ]⨾ po[vz]) ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _))) =
  po-trans wf (⊆₂-apply (addr-def₂ a8) addr[xv]) (po-trans wf po[vz] po[zy])
dob⇒po wf a8 (dob-addr-po (addr[xz] ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _))) =
  po-trans wf (⊆₂-apply (addr-def₂ a8) addr[xz]) po[zy]
dob⇒po wf a8 (dob-coi (inj₁ ctrl[xz] ⨾[ _ ]⨾ coi[zy])) =
  po-trans wf (⊆₂-apply (ctrl-def₂ a8) ctrl[xz]) (proj₂ coi[zy])
dob⇒po wf a8 (dob-coi (inj₂ data[xz] ⨾[ _ ]⨾ coi[zy])) =
  po-trans wf (⊆₂-apply (data-def₂ a8) data[xz]) (proj₂ coi[zy])
dob⇒po wf a8 (dob-rfi (inj₁ addr[xz] ⨾[ _ ]⨾ rfi[zy])) =
  po-trans wf (⊆₂-apply (addr-def₂ a8) addr[xz]) (proj₂ rfi[zy])
dob⇒po wf a8 (dob-rfi (inj₂ data[xz] ⨾[ _ ]⨾ rfi[zy])) =
  po-trans wf (⊆₂-apply (data-def₂ a8) data[xz]) (proj₂ rfi[zy])


aob⇒po : {ex : Execution LabelArmv8}
  → WellFormed ex
  → {x y : Event LabelArmv8}
  → Aob ex x y
    ----------
  → po ex x y
aob⇒po wf (aob-rmw rmw[xy]) = proj₁ (⊆₂-apply (rmw-def wf) rmw[xy])
aob⇒po wf (aob-rfi ((refl , _) ⨾[ _ ]⨾ rfi[xy] ⨾[ _ ]⨾ (refl , _))) = proj₂ rfi[xy]


dobʳ-rw : ∀ {ex : Execution LabelArmv8}
  → (wf : WellFormed ex)
  → (a8 : Armv8Execution ex)
  → {x y : Event LabelArmv8}
  → Dob a8 x y
    ----------
  → EvRW y
dobʳ-rw wf a8 (dob-addr addr[xy]) with ×₂-applyʳ (addr-def₁ a8) addr[xy]
... | inj₁ y-r = r⇒rw y-r
... | inj₂ y-w = w⇒rw y-w
dobʳ-rw wf a8 (dob-data data[xy]) = w⇒rw (×₂-applyʳ (data-def₁ a8) data[xy])
dobʳ-rw wf a8 (dob-ctrl (ctrl[xy] ⨾[ _ ]⨾ (refl , y-w))) = w⇒rw y-w
dobʳ-rw wf a8 (dob-isb (f[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-r))) = r⇒rw y-r
dobʳ-rw wf a8 (dob-addr-po (addr[xz] ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-w))) = w⇒rw y-w
dobʳ-rw wf a8 (dob-coi (_ ⨾[ _ ]⨾ coi[zy])) = w⇒rw (×₂-applyʳ (co-w×w wf) (proj₁ coi[zy]))
dobʳ-rw wf a8 (dob-rfi (_ ⨾[ _ ]⨾ rfi[zy])) = r⇒rw (×₂-applyʳ (rf-w×r wf) (proj₁ rfi[zy]))


aobʳ-rw : ∀ {ex : Execution LabelArmv8}
  → (wf : WellFormed ex)
  → {x y : Event LabelArmv8}
  → Aob ex x y
    ----------
  → EvRW y
aobʳ-rw wf (aob-rmw rmw[xy]) = wₜ⇒rw (×₂-applyʳ (rmw-r×w wf) rmw[xy])
aobʳ-rw wf (aob-rfi ((refl , _) ⨾[ _ ]⨾ rfi[xy] ⨾[ _ ]⨾ (refl , _))) = r⇒rw (×₂-applyʳ (rf-w×r wf) (proj₁ rfi[xy]))


obsˡ-rw : {ex : Execution LabelArmv8}
  → WellFormed ex
  → {x y : Event LabelArmv8}
  → Obs ex x y
    ----------
  → EvRW x
obsˡ-rw wf (obs-rfe rfe[xy]) = w⇒rw (×₂-applyˡ (rfe-w×r wf) rfe[xy])
obsˡ-rw wf (obs-coe coe[xy]) = w⇒rw (×₂-applyˡ (coe-w×w wf) coe[xy])
obsˡ-rw wf (obs-fre fre[xy]) = r⇒rw (×₂-applyˡ (fre-r×w wf) fre[xy])


obsʳ-rw : {ex : Execution LabelArmv8}
  → WellFormed ex
  → {x y : Event LabelArmv8}
  → Obs ex x y
    ----------
  → EvRW y
obsʳ-rw wf (obs-rfe rfe[xy]) = r⇒rw (×₂-applyʳ (rfe-w×r wf) rfe[xy])
obsʳ-rw wf (obs-coe coe[xy]) = w⇒rw (×₂-applyʳ (coe-w×w wf) coe[xy])
obsʳ-rw wf (obs-fre fre[xy]) = w⇒rw (×₂-applyʳ (fre-r×w wf) fre[xy])


obi⇒po/obs : {ex : Execution LabelArmv8}
  → (wf : WellFormed ex)
  → (a8 : Armv8Execution ex)
  → {x y : Event LabelArmv8}
  → Obi a8 x y
    ---------------------
  → (po ex ∪₂ Obs ex) x y
obi⇒po/obs wf a8 (obi-init ((refl , x-init) ⨾[ _ ]⨾ po[xy])) = inj₁ po[xy]
obi⇒po/obs wf a8 (obi-obs obs[xy]) = inj₂ obs[xy]
obi⇒po/obs wf a8 (obi-dob dob[xy]) = inj₁ (dob⇒po wf a8 dob[xy])
obi⇒po/obs wf a8 (obi-aob aob[xy]) = inj₁ (aob⇒po wf aob[xy])
obi⇒po/obs wf a8 (obi-bob bob[xy]) = inj₁ (bob⇒po wf bob[xy])


obiˡ∈ex : {ex : Execution LabelArmv8}
  → WellFormed ex
  → (a8 : Armv8Execution ex)
  → {x y : Event LabelArmv8}
  → Obi a8 x y
    -------------
  → x ∈ events ex
obiˡ∈ex wf a8 obi[xy] with obi⇒po/obs wf a8 obi[xy]
... | inj₁ po[xy]  = poˡ∈ex wf po[xy]
... | inj₂ obs[xy] = obsˡ∈ex wf obs[xy]
  where
  obsˡ∈ex : Obs ˡ∈ex
  obsˡ∈ex {ex} wf (obs-rfe rfe[xy]) = ⊆₁-apply (rf-elements wf) (take-udrˡ (rf ex) (proj₁ rfe[xy]))
  obsˡ∈ex {ex} wf (obs-coe coe[xy]) = ⊆₁-apply (co-elements wf) (take-udrˡ (co ex) (proj₁ coe[xy]))
  obsˡ∈ex {ex} wf (obs-fre fre[xy]) = ⊆₁-apply (fr-elements wf) (take-udrˡ (fr ex) (proj₁ fre[xy]))


obs-irreflexive : {ex : Execution LabelArmv8}
  → WellFormed ex
    ------------------------
  → Irreflexive _≡_ (Obs ex)
obs-irreflexive wf refl (obs-rfe rfe[xx]) = rf-irreflexive wf refl (proj₁ rfe[xx])
obs-irreflexive wf refl (obs-coe coe[xx]) = co-irreflexive wf refl (proj₁ coe[xx])
obs-irreflexive wf refl (obs-fre fre[xx]) = fr-irreflexive wf refl (proj₁ fre[xx])


obi-irreflexive : {ex : Execution LabelArmv8}
  → WellFormed ex
  → (a8 : Armv8Execution ex)
    ------------------------
  → Irreflexive _≡_ (Obi a8)
obi-irreflexive wf a8 refl (obi-init ((refl , x-init) ⨾[ _ ]⨾ po[xy])) = po-irreflexive wf refl po[xy]
obi-irreflexive wf a8 refl (obi-obs obs[xx]) = obs-irreflexive wf refl obs[xx]
obi-irreflexive wf a8 refl (obi-dob dob[xx]) = po-irreflexive wf refl (dob⇒po wf a8 dob[xx])
obi-irreflexive wf a8 refl (obi-aob aob[xx]) = po-irreflexive wf refl (aob⇒po wf aob[xx])
obi-irreflexive wf a8 refl (obi-bob bob[xx]) = po-irreflexive wf refl (bob⇒po wf bob[xx])
