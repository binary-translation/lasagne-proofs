{-# OPTIONS --safe #-}


-- | "Read-after-Read with fence" elimination specification
module TransformFRAR where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst; cong; cong₂) renaming (sym to ≡-sym)
open import Level using (Level; _⊔_) renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim; ⊥)
open import Data.Product using (_×_; _,_; ∃-syntax; map₂; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Tri)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.LIMM as LIMM


open Execution


--
-- FRAR: a = X; F; b = X  ->  a = X; F; b = a
--                 ^
--                 |
--                This Read becomes a Skip
--

record FRAR-Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsLIMMConsistent ex
    
    pres₁-ev  : Event LabelLIMM
    pres₁-rₜ  : EvRₜ tmov pres₁-ev
    
    pres₂-ev : Event LabelLIMM
    pres₂-f  : EvF pres₂-ev

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelLIMM
    elim-ev-skip : EvSkip elim-ev

    pair₁-pi : po-imm ex pres₁-ev pres₂-ev
    pair₂-pi : po-imm ex pres₂-ev elim-ev

    -- Note that we -- specifically -- assume the execution was obtained by /mapping from x86/.
    -- That is, every read operation is directly followed by a F_RM fence.
    po-r-rm : {x : Event LabelLIMM} → x ∈ events ex → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm ex x y)


module Extra {ex : Execution LabelLIMM} (ex-ok : FRAR-Restricted ex) where

  open FRAR-Restricted ex-ok


  pres₁-r : EvR pres₁-ev
  pres₁-r = rₜ⇒r pres₁-rₜ

  elim-uid : UniqueId
  elim-uid = ev-uid elim-ev

  elim-has-uid : HasUid elim-uid elim-ev
  elim-has-uid = ev-has-uid _

  elim-tid : ThreadId
  elim-tid = skip-tid elim-ev-skip

  elim-loc : Location
  elim-loc = r-loc pres₁-r

  elim-val : Value
  elim-val = r-val pres₁-r

  pres₁∈ex : pres₁-ev ∈ events ex
  pres₁∈ex = piˡ∈ex wf pair₁-pi

  pres₂∈ex : pres₂-ev ∈ events ex
  pres₂∈ex = piˡ∈ex wf pair₂-pi

  elim∈ex : elim-ev ∈ events ex
  elim∈ex = piʳ∈ex wf pair₂-pi

  pres₁-has-loc : HasLoc elim-loc pres₁-ev
  pres₁-has-loc = r-has-loc pres₁-r

  pres₁-has-val : HasVal elim-val pres₁-ev
  pres₁-has-val = r-has-val pres₁-r


-- | Relates the source and target executions.
--
-- If the source has the additional read event, then - by WellFormedness - it is part of the execution.
record FRARMapping (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-ok : FRAR-Restricted dst) : Set where
  open FRAR-Restricted dst-ok
  open Extra dst-ok

  field
    src-elim-ev     : Event LabelLIMM
    src-elim-ev-def : src-elim-ev ≡ event elim-uid elim-tid (lab-r tmov elim-loc elim-val)
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelLIMM} → x ≢ elim-ev → x ∈ events dst → x ∈ events src
