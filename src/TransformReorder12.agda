{-# OPTIONS --safe #-}


-- | Reorders one event with two events
--
-- > a ∘ (b ∘ c)  →  (b ∘ c) ∘ a
module TransformReorder12 where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (_∈_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.LIMM


open Execution
open WellFormed


--
-- This specification describes that a /successful/ RMW can move - to the left - over any fence.
--
-- > F ; RMW  →  RMW ; F
--
-- Note that a failed RMW - represented by only a `Rₜ trmw` event - can also move over
-- some events; But this is proved in `Proof.Reorder.Single`.
--


-- # Definitions

-- 
-- Note that this structure describes the /target/.
record ReorderRestricted12 (ex : Execution LabelLIMM) : Set₁ where
  field
    consistent : IsLIMMConsistent ex
    wellformed : WellFormed ex

    -- Left (both rmw events)
    ev₁ : Event LabelLIMM
    ev₂ : Event LabelLIMM
    -- Right (fence)
    ev₃ : Event LabelLIMM

    ev₃-f : EvF ev₃

    rmw₁₂ᵗ : rmw ex ev₁ ev₂
    pi₂₃ᵗ  : po-imm ex ev₂ ev₃


-- | Relates the source and target executions. They are mostly identical, except for the reordered pair.
record ReordersTo12 (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-ok : ReorderRestricted12 dst) : Set₁ where
  open ReorderRestricted12 dst-ok
  
  field
    events-preserved : events src ⇔₁ events dst
    co-preserved     : co src  ⇔₂ co dst
    rf-preserved     : rf src  ⇔₂ rf dst
    rmw-preserved    : rmw src ⇔₂ rmw dst

    po-preserved⇒ : ∀ {x y : Event LabelLIMM} → ¬ (x ≡ ev₃ × y ≡ ev₁) → ¬ (x ≡ ev₃ × y ≡ ev₂) → po src x y → po dst x y
    po-preserved⇐ : ∀ {x y : Event LabelLIMM} → ¬ (x ≡ ev₁ × y ≡ ev₃) → ¬ (x ≡ ev₂ × y ≡ ev₃) → po dst x y → po src x y
    

-- # Operations

module Extra {ex : Execution LabelLIMM} (ex-res : ReorderRestricted12 ex) where

  open ReorderRestricted12 ex-res

  private
    wf = wellformed


  ev₁-rₐ : EvRₜ trmw ev₁
  ev₁-rₐ = rmwˡ-r wf (take-dom (rmw ex) rmw₁₂ᵗ)

  ev₁-r : EvR ev₁
  ev₁-r = rₜ⇒r ev₁-rₐ

  ev₂-wₐ : EvWₜ trmw ev₂
  ev₂-wₐ = rmwʳ-w wf (take-codom (rmw ex) rmw₁₂ᵗ)

  ev₂-w : EvW ev₂
  ev₂-w = wₜ⇒w ev₂-wₐ


  pi₁₂ᵗ : po-imm ex ev₁ ev₂
  pi₁₂ᵗ = ⊆₂-apply (rmw-def wf) rmw₁₂ᵗ

  po₁₂ᵗ : po ex ev₁ ev₂
  po₁₂ᵗ = proj₁ pi₁₂ᵗ

  po₂₃ᵗ : po ex ev₂ ev₃
  po₂₃ᵗ = proj₁ pi₂₃ᵗ

  po₁₃ᵗ : po ex ev₁ ev₃
  po₁₃ᵗ = po-trans wf po₁₂ᵗ po₂₃ᵗ


  ¬init₁ : ¬ EvInit ev₁
  ¬init₁ init₁ = disjoint-r/init _ (ev₁-r , init₁)

  ¬init₂ : ¬ EvInit ev₂
  ¬init₂ init₂ = disjoint-wₜ/init _ (ev₂-wₐ , init₂)

  ¬init₃ : ¬ EvInit ev₃
  ¬init₃ init₃ = disjoint-f/init _ (ev₃-f , init₃)
  

  ¬po₂₁ᵗ : ¬ po ex ev₂ ev₁
  ¬po₂₁ᵗ = po-irreflexive wf refl ∘ po-trans wf po₁₂ᵗ
  
  ¬po₃₁ᵗ : ¬ po ex ev₃ ev₁
  ¬po₃₁ᵗ = po-irreflexive wf refl ∘ po-trans wf po₁₃ᵗ


  ev₁∈ex : ev₁ ∈ events ex
  ev₁∈ex = poˡ∈ex wf po₁₂ᵗ

  ev₂∈ex : ev₂ ∈ events ex
  ev₂∈ex = poʳ∈ex wf po₁₂ᵗ

  ev₃∈ex : ev₃ ∈ events ex
  ev₃∈ex = poʳ∈ex wf po₂₃ᵗ


  ev₁≢ev₂ : ev₁ ≢ ev₂
  ev₁≢ev₂ 1≡2 = po-irreflexive wf 1≡2 po₁₂ᵗ

  ev₁≢ev₃ : ev₁ ≢ ev₃
  ev₁≢ev₃ 1≡3 = po-irreflexive wf 1≡3 po₁₃ᵗ

  ev₂≢ev₃ : ev₂ ≢ ev₃
  ev₂≢ev₃ 2≡3 = po-irreflexive wf 2≡3 po₂₃ᵗ
