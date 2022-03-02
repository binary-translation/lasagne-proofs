{-# OPTIONS --safe #-}

module Arch.X86 where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary using (_⇔_)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Helpers
open import Arch.General.Event
open import Arch.General.Properties using (tag-eq-dec; ev-eq-dec)
open import Arch.General.Execution


open Event
open Execution


-- # Definitions

data LabelX86 : Set where
  lab-r : Tag → Location → Value → LabelX86 -- ^ read
  lab-w : Tag → Location → Value → LabelX86 -- ^ write
  lab-f : LabelX86 -- ^ fence

data LabR : LabelX86 → Set where
  is-r : ∀ {tag : Tag} {loc : Location} {val : Value} → LabR (lab-r tag loc val)

data LabW : LabelX86 → Set where
  is-w : ∀ {tag : Tag} {loc : Location} → {val : Value} → LabW (lab-w tag loc val)

data LabF : LabelX86 → Set where
  is-f : LabF lab-f


-- # Lemmas/Properties

private

  labs-xopt : XOptPred₃ LabR LabW LabF
  labs-xopt (lab-r _ _ _) = xopt₁ is-r  (λ()) (λ())
  labs-xopt (lab-w _ _ _) = xopt₂ (λ()) is-w  (λ())
  labs-xopt lab-f         = xopt₃ (λ()) (λ()) is-f

  r-unique : UniquePred LabR
  r-unique _ is-r is-r = refl

  w-unique : UniquePred LabW
  w-unique _ is-w is-w = refl

  f-unique : UniquePred LabF
  f-unique _ is-f is-f = refl

  r-tag : {lab : LabelX86} → LabR lab → Tag
  r-tag {lab-r tag _ _} is-r = tag

  w-tag : {lab : LabelX86} → LabW lab → Tag
  w-tag {lab-w tag _ _} is-w = tag

  r-loc : {lab : LabelX86} → LabR lab → Location
  r-loc {lab-r _ loc _} is-r = loc

  r-val : {lab : LabelX86} → LabR lab → Value
  r-val {lab-r _ _ val} is-r = val

  w-loc : {lab : LabelX86} → LabW lab → Location
  w-loc {lab-w _ loc _} is-w = loc

  w-val : {lab : LabelX86} → LabW lab → Value
  w-val {lab-w _ _ val} is-w = val

  lab-eq-dec : DecRel (_≡_ {_} {LabelX86})
  lab-eq-dec (lab-r tag₁ loc₁ val₁) (lab-r tag₂ loc₂ val₂) =
    cong₃-dec lab-r
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-w tag₁ loc₁ val₁) (lab-w tag₂ loc₂ val₂) =
    cong₃-dec lab-w
      (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl})
      (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec lab-f lab-f = yes refl
  -- unequal cases
  lab-eq-dec (lab-r _ _ _) (lab-w _ _ _) = no (λ())
  lab-eq-dec (lab-r _ _ _) lab-f         = no (λ())
  lab-eq-dec (lab-w _ _ _) (lab-r _ _ _) = no (λ())
  lab-eq-dec (lab-w _ _ _) lab-f         = no (λ())
  lab-eq-dec lab-f         (lab-r _ _ _) = no (λ())
  lab-eq-dec lab-f         (lab-w _ _ _) = no (λ())


instance
  LabelX86-ok : LabelClass LabelX86
  LabelX86-ok =
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


data EvR₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelX86 → Set where
  ev-r : {uid : UniqueId} {tid : ThreadId} → EvR₌ tag loc val (event uid tid (lab-r tag loc val))
  
data EvW₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelX86 → Set where
  ev-w₌ : {uid : UniqueId} {tid : ThreadId} → EvW₌ tag loc val (event uid tid (lab-w tag loc val))


-- X86 Implied order
data Implied (ex : Execution LabelX86) (x y : Event LabelX86) : Set where
  implied-pof : ( po ex ⨾ ⦗ dom (rmw ex) ∪₁ EvF ⦘ )   x y → Implied ex x y
  implied-fpo : ( ⦗ codom (rmw ex) ∪₁ EvF ⦘ ⨾ po ex ) x y → Implied ex x y

-- X86 Preserved Program Order
data Xppo (ex : Execution LabelX86) (x y : Event LabelX86) : Set where
  xppo-w×w : ( (EvW ×₂ EvW) ∩₂ (po ex) ) x y → Xppo ex x y
  xppo-r×w : ( (EvR ×₂ EvW) ∩₂ (po ex) ) x y → Xppo ex x y
  xppo-r×r : ( (EvR ×₂ EvR) ∩₂ (po ex) ) x y → Xppo ex x y

-- X86 Happens Before
data Xhb (ex : Execution LabelX86) (x y : Event LabelX86) : Set where
  -- By definition, init events occur before any other events in the execution
  xhb-init    : ( ⦗ EvInit ⦘ ⨾ po ex ) x y → Xhb ex x y
  -- The XHB relations
  xhb-xppo    : Xppo ex                x y → Xhb ex x y
  xhb-implied : Implied ex             x y → Xhb ex x y
  xhb-rfe     : rfe ex                 x y → Xhb ex x y
  xhb-fr      : fr ex                  x y → Xhb ex x y
  xhb-co      : co ex                  x y → Xhb ex x y
  

record IsX86Consistent (ex : Execution LabelX86) : Set₁ where
  field
    -- # Consistency axioms

    ax-coherence  : Acyclic _≡_ ( po-loc ex ∪₂ rf ex ∪₂ fr ex ∪₂ co ex )
    ax-atomicity  : Empty₂ (rmw ex ∩₂ (fre ex ⨾ coe ex))
    ax-ghb        : Acyclic _≡_ (Xhb ex)


-- # Helpers

xppo⇒po : {ex : Execution LabelX86} {x y : Event LabelX86} → Xppo ex x y → po ex x y
xppo⇒po (xppo-w×w (_ , po[xy])) = po[xy]
xppo⇒po (xppo-r×w (_ , po[xy])) = po[xy]
xppo⇒po (xppo-r×r (_ , po[xy])) = po[xy]

implied⇒po : {ex : Execution LabelX86} {x y : Event LabelX86} → Implied ex x y → po ex x y
implied⇒po (implied-pof (po[xy] ⨾[ _ ]⨾ (refl , _))) = po[xy]
implied⇒po (implied-fpo ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
