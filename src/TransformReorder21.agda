{-# OPTIONS --safe #-}


-- | Reorders two events with one event
--
-- > (a ∘ b) ∘ c  →  c ∘ (a ∘ b)
module TransformReorder21 where

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
-- This specification describes that a /successful/ RMW can move - to the right - over any fence.
--
-- > RMW ; F  →  F ; RMW
--
-- Note that a failed RMW - represented by only a `Rₜ trmw` event - can also move over
-- some events; But this is proved in `Proof.Reorder.Single`.
--


-- # Definitions

-- | A proof stating the /target/ execution could only have been generated from a
-- program that is mapped through the reordering transformation.
--
--
-- # Order
--
-- Note that the /target/ order is:
--
-- > ev₁  -pi-  ev₂  -rmw-  ev₃
--
-- While the /source/ order is:
--
-- > ev₂  -rmw-  ev₃  -pi-  ev₁
record ReorderRestricted21 (ex : Execution LabelLIMM) : Set₁ where
  field
    consistent : IsLIMMConsistent ex
    wellformed : WellFormed ex

    -- Left (fence)
    ev₁ : Event LabelLIMM
    -- Right (both rmw events)
    ev₂ : Event LabelLIMM
    ev₃ : Event LabelLIMM

    ev₁-f : EvF ev₁

    pi₁₂ᵗ  : po-imm ex ev₁ ev₂
    rmw₂₃ᵗ : rmw ex ev₂ ev₃


-- | Relates the events in the source and target executions, following the
-- transformation on the instructions.
--
-- They are mostly identical, except for the reordered pair.
record ReordersTo21 (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-ok : ReorderRestricted21 dst) : Set₁ where
  open ReorderRestricted21 dst-ok
  
  field
    events-preserved : events src ⇔₁ events dst
    co-preserved     : co src  ⇔₂ co dst
    rf-preserved     : rf src  ⇔₂ rf dst
    rmw-preserved    : rmw src ⇔₂ rmw dst

    po-preserved⇒ : ∀ {x y : Event LabelLIMM} → ¬ (x ≡ ev₂ × y ≡ ev₁) → ¬ (x ≡ ev₃ × y ≡ ev₁) → po src x y → po dst x y
    po-preserved⇐ : ∀ {x y : Event LabelLIMM} → ¬ (x ≡ ev₁ × y ≡ ev₂) → ¬ (x ≡ ev₁ × y ≡ ev₃) → po dst x y → po src x y
    

-- # Operations

module Extra {ex : Execution LabelLIMM} (ex-res : ReorderRestricted21 ex) where

  open ReorderRestricted21 ex-res

  private
    wf = wellformed


  ev₂-rₐ : EvRₜ trmw ev₂
  ev₂-rₐ = rmwˡ-r wf (take-dom (rmw ex) rmw₂₃ᵗ)

  ev₂-r : EvR ev₂
  ev₂-r = rₜ⇒r ev₂-rₐ

  ev₃-wₐ : EvWₜ trmw ev₃
  ev₃-wₐ = rmwʳ-w wf (take-codom (rmw ex) rmw₂₃ᵗ)

  ev₃-w : EvW ev₃
  ev₃-w = wₜ⇒w ev₃-wₐ

  pi₂₃ᵗ : po-imm ex ev₂ ev₃
  pi₂₃ᵗ = ⊆₂-apply (rmw-def wf) rmw₂₃ᵗ

  po₁₂ᵗ : po ex ev₁ ev₂
  po₁₂ᵗ = proj₁ pi₁₂ᵗ

  po₂₃ᵗ : po ex ev₂ ev₃
  po₂₃ᵗ = proj₁ pi₂₃ᵗ

  po₁₃ᵗ : po ex ev₁ ev₃
  po₁₃ᵗ = po-trans wf po₁₂ᵗ po₂₃ᵗ


  ¬init₁ : ¬ EvInit ev₁
  ¬init₁ init₁ = disjoint-f/init _ (ev₁-f , init₁)

  ¬init₂ : ¬ EvInit ev₂
  ¬init₂ init₂ = disjoint-r/init _ (ev₂-r , init₂)

  ¬init₃ : ¬ EvInit ev₃
  ¬init₃ init₃ = disjoint-wₜ/init _ (ev₃-wₐ , init₃)


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
