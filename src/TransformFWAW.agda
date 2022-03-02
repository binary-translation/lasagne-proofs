{-# OPTIONS --safe #-}


-- | "Write-after-Write with fence" elimination
module TransformFWAW where

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
-- FWAW: X = v'; F; X = v  ↦  F; X = v
--       ^
--       |
--      This Write becomes a Skip
--


record FWAW-Restricted (ex : Execution LabelLIMM) : Set₁ where
  field
    wf : WellFormed ex
    consistent : IsLIMMConsistent ex

    -- | The skip event that overwrites the eliminated read.
    elim-ev      : Event LabelLIMM
    elim-ev-skip : elim-ev ∈ EvSkip

    -- preserved event 1
    pres₁-ev  : Event LabelLIMM
    pres₁-f   : EvF pres₁-ev

    -- preserved event 2
    pres₂-ev  : Event LabelLIMM
    -- non-init relaxed write
    pres₂-wₙᵣ : EvWₙₜ tmov pres₂-ev

    pi[ep₁]ᵗ  : po-imm ex elim-ev pres₁-ev
    pi[p₁p₂]ᵗ : po-imm ex pres₁-ev pres₂-ev

    -- Note that we -- specifically -- assume the execution was obtained by /mapping from x86/.
    -- That is, every read operation is directly /followed by/ a F_RM fence.
    po-r-rm : {x : Event LabelLIMM} → x ∈ events ex → EvRᵣ x → ∃[ y ] (EvF₌ RM y × po-imm ex x y)
    -- Every write operation is directly /preceded by/ a F_WW fence.
    po-w-ww : {y : Event LabelLIMM} → y ∈ events ex → EvWₙₜ tmov y → ∃[ x ] (EvF₌ WW x × po-imm ex x y)


module Extra {ex : Execution LabelLIMM} (ex-ok : FWAW-Restricted ex) where

  open FWAW-Restricted ex-ok
  

  pres₂-wᵣ : EvWᵣ pres₂-ev
  pres₂-wᵣ = wₙₜ⇒wₜ pres₂-wₙᵣ

  pres₂-w : EvW pres₂-ev
  pres₂-w = wₜ⇒w pres₂-wᵣ

  elim-uid : UniqueId
  elim-uid = ev-uid elim-ev

  elim-has-uid : HasUid elim-uid elim-ev
  elim-has-uid = ev-has-uid _

  elim-tid : ThreadId
  elim-tid = skip-tid elim-ev-skip

  elim-loc : Location
  elim-loc = w-loc pres₂-w

  elim-val : Value
  elim-val = w-val pres₂-w


  pres₁∈ex : pres₁-ev ∈ events ex
  pres₁∈ex = piʳ∈ex wf pi[ep₁]ᵗ

  pres₂∈ex : pres₂-ev ∈ events ex
  pres₂∈ex = piʳ∈ex wf pi[p₁p₂]ᵗ

  elim∈ex : elim-ev ∈ events ex
  elim∈ex = piˡ∈ex wf pi[ep₁]ᵗ


  pres₂-has-loc : HasLoc elim-loc pres₂-ev
  pres₂-has-loc = w-has-loc pres₂-w

  pres₂-has-val : HasVal elim-val pres₂-ev
  pres₂-has-val = w-has-val pres₂-w
  
  po[ep₂]ᵗ : po ex elim-ev pres₂-ev
  po[ep₂]ᵗ = po-trans wf (proj₁ pi[ep₁]ᵗ) (proj₁ pi[p₁p₂]ᵗ)


-- | Relates the source and target executions.
--
-- If the source has the additional write event, then - by WellFormedness - it is part of the execution.
record FWAWMapping (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-res : FWAW-Restricted dst) : Set where
  open FWAW-Restricted dst-res
  open Extra dst-res

  field
    src-elim-ev     : Event LabelLIMM
    src-elim-ev-def : src-elim-ev ≡ event elim-uid elim-tid (lab-w tmov elim-loc elim-val)
    src-elim-ev∈src : src-elim-ev ∈ events src

    events-preserved : ∀ {x : Event LabelLIMM} → x ≢ elim-ev → x ∈ events dst → x ∈ events src
