{-# OPTIONS --safe #-}


-- | "Read-after-write with fence" elimination specification
module TransformFRAW where

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
-- FRAW: X = v; F; a = X  ->  X = v; F; a = v
--                 ^
--                 |
--                This Read becomes a Skip
--


record FRAW-Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsLIMMConsistent ex

    pres₁-ev  : Event LabelLIMM
    pres₁-wₙᵣ : EvWₙₜ tmov pres₁-ev
    
    pres₂-ev : Event LabelLIMM
    pres₂-f  : EvF pres₂-ev

    -- | The skip event that overwrites the eliminated read.
    elim-ev   : Event LabelLIMM
    elim-skip : EvSkip elim-ev

    pi[p₁p₂]ᵗ : po-imm ex pres₁-ev pres₂-ev
    pi[p₂e]ᵗ  : po-imm ex pres₂-ev elim-ev

    -- We /specifically/ assume the execution was obtained by /mapping from x86/.
    -- That is, every read operation is directly /followed by/ a F_RM fence.
    po-r-rmʳ : {x : Event LabelLIMM} → x ∈ events ex → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm ex x y)
    po-r-rmˡ : {y : Event LabelLIMM} → y ∈ events ex → EvF₌ RM y → ∃[ x ] (EvRᵣ x × po-imm ex x y)
    -- Every write operation is directly /preceded by/ a F_WW fence.
    po-w-wwˡ : {y : Event LabelLIMM} → y ∈ events ex → EvWₙₜ tmov y → ∃[ x ] (EvF₌ WW x × po-imm ex x y)
    po-w-wwʳ : {x : Event LabelLIMM} → x ∈ events ex → EvF₌ WW x → ∃[ y ] (EvWₙₜ tmov y × po-imm ex x y)


module Extra {ex : Execution LabelLIMM} (ex-ok : FRAW-Restricted ex) where

  open FRAW-Restricted ex-ok


  pres₁-w : EvW pres₁-ev
  pres₁-w = wₙₜ⇒w pres₁-wₙᵣ

  pres₁-wᵣ : EvWᵣ pres₁-ev
  pres₁-wᵣ = wₙₜ⇒wₜ pres₁-wₙᵣ

  pres₁∈ex : pres₁-ev ∈ events ex
  pres₁∈ex = piˡ∈ex wf pi[p₁p₂]ᵗ

  pres₂∈ex : pres₂-ev ∈ events ex
  pres₂∈ex = piʳ∈ex wf pi[p₁p₂]ᵗ

  elim∈ex : elim-ev ∈ events ex
  elim∈ex = piʳ∈ex wf pi[p₂e]ᵗ

  pres₂-mode : ∃[ mode ] (EvF₌ mode pres₂-ev)
  pres₂-mode with pres₂-ev | pres₂-f
  ... | event _ _ (lab-f mode) | ev-f is-f = mode , ev-f₌

  elim-uid : UniqueId
  elim-uid = ev-uid elim-ev

  elim-has-uid : HasUid elim-uid elim-ev
  elim-has-uid = ev-has-uid elim-ev

  elim-tid : ThreadId
  elim-tid = skip-tid elim-skip

  elim-loc : Location
  elim-loc = w-loc pres₁-w

  elim-val : Value
  elim-val = w-val pres₁-w

  pres₁-has-loc : HasLoc elim-loc pres₁-ev
  pres₁-has-loc = w-has-loc pres₁-w

  pres₁-has-val : HasVal elim-val pres₁-ev
  pres₁-has-val = w-has-val pres₁-w


-- | Relates the events in the source and target executions, following the
-- transformation on the instructions.
--
-- If the source has the additional read event, then - by WellFormedness -
-- it is part of the execution.
record FRAWMapping (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-res : FRAW-Restricted dst) : Set where
  open FRAW-Restricted dst-res
  open Extra dst-res

  field
    src-elim-ev     : Event LabelLIMM
    src-elim-ev-def : src-elim-ev ≡ event elim-uid elim-tid (lab-r tmov elim-loc elim-val)
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelLIMM} → x ≢ elim-ev → x ∈ events dst → x ∈ events src
