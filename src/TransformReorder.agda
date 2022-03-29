{-# OPTIONS --safe #-}

-- | Reorders one event with one other event
--
-- > a ∘ b  →  b ∘ a
module TransformReorder where

-- Stdlib imports
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (_∈_)
-- Library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.LIMM


open Execution


-- # Definitions

--
-- The table of valid reorders specified by this description. ("X" means valid)
-- Note that the holes are covered by the rules in `ReorderRestricted`.
--
-- a \ b | Rᵣ    | Wᵣ    | Rₐ    | F_RM  | F_WW  | F_SC
-- ------+-------+-------+-------+-------+-------+-----
-- Rᵣ    | X     | X     | X     |       | X     |  
-- Wᵣ    | X     | X     | X     | X     |       |  
-- Rₐ    |       |       |       | X     | X     | X
-- F_RM  |       |       |       | X     | X     | X
-- F_WW  | X     |       | X     | X     | X     | X
-- F_SC  |       |       |       | X     | X     | X
--
--
-- In the table, `Rₐ` represents a /failed RMW/ operation.
-- Note that this file only specifies reordering single events. The successful
-- RMW pairs (Rₐ - Wₐ) are proven elsewhere. (See `TransformReorder12` and
-- `TransformReorder21`)
--


-- | A proof stating the /target/ execution could only have been generated from a
-- program that is mapped through the reordering transformation.
--
--
-- # Order
--
-- Note that the /target/ order is:
--
-- > ev₁  -pi-  ev₂
--
-- While the /source/ order is:
--
-- > ev₂  -pi-  ev₁
record ReorderRestricted (ex : Execution LabelLIMM) : Set₁ where
  field
    consistent : IsLIMMConsistent ex
    wellformed : WellFormed ex
    
    ev₁ : Event LabelLIMM
    ev₂ : Event LabelLIMM

    ¬same-loc : ¬ SameLoc ev₁ ev₂
    ¬init₁ : ¬ EvInit ev₁
    ¬init₂ : ¬ EvInit ev₂

    ¬skip₁ : ¬ EvSkip ev₁
    ¬skip₂ : ¬ EvSkip ev₂

    -- /Individual events/ in a successful RMWs cannot reorder. (because it consists of 2 events)
    -- However, there is another proof for reordering RMWs with fences.
    ¬rmw₁ : ¬ (ev₁ ∈ udr (rmw ex))
    ¬rmw₂ : ¬ (ev₂ ∈ udr (rmw ex))
    

    -- Note that `ev₂`-`ev₁` is the /order in the source/.
    -- While `ev₁`-`ev₂` is the /order in the target/.

    -- The rules below specify which pairs /cannot/ reorder.
    -- Any pairs /not/ covered by these, /can reorder/.

    -- Note that /failed rmw reads/ can reorder with RM fences (to the right)
    pord-rmˡ : ¬ (EvRₜ tmov ev₂ × EvF₌ RM ev₁)
    pord-rmʳ : ¬ (EvF₌ RM ev₂ × EvRW ev₁)

    pord-wwˡ : ¬ (EvW ev₂ × EvF₌ WW ev₁)
    pord-wwʳ : ¬ (EvF₌ WW ev₂ × EvW ev₁)

    -- A /failed rmw read/ can move over a SC fence (to the right)
    pord-scˡ : ¬ ((EvRₜ tmov ∪₁ EvW) ev₂ × EvF₌ SC ev₁)
    pord-scʳ : ¬ (EvF₌ SC ev₂ × EvRW ev₁)

    -- A RMW-read is ordered with whatever follows, even if the RMW is unsuccessful
    -- (See `ord-r` in LIMM's `Ord` relation)
    pord-rmw-rʳ : ¬ (EvRₜ trmw ev₂ × EvRW ev₁)

    pi[12]ᵗ : po-imm ex ev₁ ev₂


-- | Relates the events in the source and target executions, following the
-- transformation on the instructions.
--
-- They are mostly identical, except for the reordered pair.
record ReordersTo (src : Execution LabelLIMM) {dst : Execution LabelLIMM} (dst-ok : ReorderRestricted dst) : Set₁ where
  open ReorderRestricted dst-ok
  
  field
    events-preserved : events src ⇔₁ events dst
    co-preserved     : co src  ⇔₂ co dst
    rf-preserved     : rf src  ⇔₂ rf dst
    rmw-preserved    : rmw src ⇔₂ rmw dst

    po-preserved⇒ : ∀ {x y : Event LabelLIMM} → ¬ (x ≡ ev₂ × y ≡ ev₁) → po src x y → po dst x y
    po-preserved⇐ : ∀ {x y : Event LabelLIMM} → ¬ (x ≡ ev₁ × y ≡ ev₂) → po dst x y → po src x y


-- # Operations

-- | Helpers. The definitions and properties are derived from `ReorderRestricted` alone.
module Extra {ex : Execution LabelLIMM} (δ : ReorderRestricted ex) where

  open ReorderRestricted δ

  po[12]ᵗ : po ex ev₁ ev₂
  po[12]ᵗ = proj₁ pi[12]ᵗ
    
  ev₁∈poˡ : ev₁ ∈ dom (po ex)
  ev₁∈poˡ = take-dom (po ex) po[12]ᵗ

  ev₂∈poʳ : ev₂ ∈ codom (po ex)
  ev₂∈poʳ = take-codom (po ex) po[12]ᵗ

  ev₁∈po : ev₁ ∈ udr (po ex)
  ev₁∈po = take-udrˡ (po ex) po[12]ᵗ

  ev₂∈po : ev₂ ∈ udr (po ex)
  ev₂∈po = take-udrʳ (po ex) po[12]ᵗ

  ev₁∈ex : ev₁ ∈ events ex
  ev₁∈ex = poˡ∈ex wellformed po[12]ᵗ

  ev₂∈ex : ev₂ ∈ events ex
  ev₂∈ex = poʳ∈ex wellformed po[12]ᵗ

  ¬po[21]ᵗ : ¬ po ex ev₂ ev₁
  ¬po[21]ᵗ po[21] =
    let po[22] = po-trans wellformed po[21] po[12]ᵗ
    in po-irreflexive wellformed refl po[22]
