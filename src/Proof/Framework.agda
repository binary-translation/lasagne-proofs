{-# OPTIONS --safe #-}

open import Arch.General.Event using (LabelClass)
import Arch.General.Execution as Ex


-- | A general framework for writing proofs.
--
-- This framework is shared between architecture-mapping proofs, elimination proofs,
-- and reordering proofs.
module Proof.Framework (LabelSrc : Set) {{_ : LabelClass LabelSrc}}
  {LabelDst : Set} {{_ : LabelClass LabelDst}}
  (dst : Ex.Execution LabelDst) (dst-wf : Ex.WellFormed dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst; cong) renaming (sym to ≡-sym)
open import Level using () renaming (zero to ℓzero)
open import Function using (_∘_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers using (contrapositive)
-- Local imports: Architecture Definitions
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.DerivedWellformed


--
-- File Structure:
-- > Definitions
--   > Execution
--   > Event Mappings
--   > Types
--   > Mapping Combinators
-- > GeneralFramework - ψ
-- > WellFormed
--   > Mapping
--     > Primitives
--     > Predicates
--     > Relations
--     > Derived Predicates
--   > WellFormed Fields
--


--
-- # Notations
--
-- We use the following notations:
-- * [⇒]  - source-to-target mapping, defined in terms of source events
-- * [⇐]  - target-to-source mapping, defined in terms of target events
-- * [$⇒] - source-to-target mapping, defined in terms of target events
-- * [⇐$] - target-to-source mapping, defined in terms of source events
--
-- Examples:
-- * P[⇒]  : P x → P (ev[⇒] x∈src)
-- * P[⇐]  : P x → P (ev[⇐] x∈dst)
-- * P[$⇒] : P (ev[⇐] x∈dst) → P x
-- * P[⇐$] : P (ev[⇒] x∈src) → P x
--
-- The `[$⇒]/[⇐$]` definitions may seem somewhat clumsy, but are often useful.
-- For instance, `[⇐]` and `[$⇒]` are defined in terms of the /target/, from
-- which the /source/ is derived. Their corresponding `[⇐$]` and `[⇒]` mappings
-- can easily be derived (e.g., see `[⇐]→₁[⇐$]`).
--


open Ex.Execution
open Ex.WellFormed


module Definitions (ev[⇐] : {x : Event LabelDst} → (x∈dst : x ∈ events dst) → Event LabelSrc) where

  -- # Execution

  src-events : Pred (Event LabelSrc) ℓzero
  src-events x-src = ∃[ x-dst ] ∃[ x∈dst ] (x-src ≡ ev[⇐] {x-dst} x∈dst)


  -- | Many relations are verbatim mapped to the source. This function generalizes over that.
  --
  -- # Use Cases
  --
  -- Though, /which/ relations are mapped verbatim differs per proof.
  -- * `po`      - for mapping and elimination proofs (but not reorder)
  -- * `rf`/`co` - for mapping and reorder proofs (but not elimination)
  -- * `rmw`     - for any proof
  src-rel : {R : Rel (Event LabelDst) ℓzero}
    → (∀ {x y} → R x y → x ∈ events dst)
    → (∀ {x y} → R x y → y ∈ events dst)
    → Rel (Event LabelSrc) ℓzero
  src-rel Rˡ∈ex Rʳ∈ex x-src y-src =
    ∃[ x-dst ] ∃[ y-dst ] ∃[ dst-rmw[xy] ]
      let x∈dst = Rˡ∈ex dst-rmw[xy]
          y∈dst = Rʳ∈ex dst-rmw[xy]
      in (x-src ≡ ev[⇐] {x-dst} x∈dst × y-src ≡ ev[⇐] {y-dst} y∈dst)


  src-rmw : Rel (Event LabelSrc) ℓzero
  src-rmw = src-rel (rmwˡ∈ex dst-wf) (rmwʳ∈ex dst-wf)


  -- # Event Mappings

  -- | Maps a source event to its corresponding event in the target
  --
  -- Note that this requires a /proof that the event is in the source/.
  ev[⇒] : {x : Event LabelSrc}
    → (x∈src : x ∈ src-events)
      ------------------------
    → Event LabelDst
  ev[⇒] = proj₁


  events[⇒] : {x : Event LabelSrc}
    → (x∈src : x ∈ src-events)
      --------------------------
    → (ev[⇒] x∈src) ∈ events dst
  events[⇒] (_ , x∈dst , _) = x∈dst


  events[⇐] : {x : Event LabelDst}
    → (x∈dst : x ∈ events dst)
      ----------------------------
    → (ev[⇐] x∈dst) ∈ src-events
  events[⇐] {x} x∈dst = (x , x∈dst , refl)


  -- | Starting with event `x` in the source: Mapping `x` to the target,
  -- then mapping the result to the source, gives `x` again.
  ev[⇒⇐] : {x : Event LabelSrc}
    → (x∈src : x ∈ src-events)
      -----------------------------
    → x ≡ ev[⇐] (events[⇒] x∈src)
  ev[⇒⇐] {x-src} (x-dst , x∈dst , refl) = refl
  

  -- # Types
  
  Pred[⇒] : Pred (Event LabelSrc) ℓzero → Pred (Event LabelDst) ℓzero → Set
  Pred[⇒] Pˢ Pᵗ =
    ∀ {x}
    → (x∈src : x ∈ src-events)
    → Pˢ x
      ------------------------
    → Pᵗ (ev[⇒] x∈src)

  Pred[⇐$] : Pred (Event LabelSrc) ℓzero → Pred (Event LabelDst) ℓzero → Set
  Pred[⇐$] Pˢ Pᵗ =
    ∀ {x}
    → (x∈src : x ∈ src-events)
    → Pᵗ (ev[⇒] x∈src)
      ------------------------
    → Pˢ x

  Pred[$⇒] : Pred (Event LabelSrc) ℓzero → Pred (Event LabelDst) ℓzero → Set
  Pred[$⇒] Pˢ Pᵗ =
    ∀ {x}
    → (x∈dst : x ∈ events dst)
    → Pˢ (ev[⇐] x∈dst)
      ------------------------
    → Pᵗ x
    
  Pred[⇐] : Pred (Event LabelSrc) ℓzero → Pred (Event LabelDst) ℓzero → Set
  Pred[⇐] Pˢ Pᵗ =
    ∀ {x}
    → (x∈dst : x ∈ events dst)
    → Pᵗ x
      ------------------------
    → Pˢ (ev[⇐] x∈dst)


  Pred[⇒]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Pred (Event Label) ℓzero) → Set
  Pred[⇒]² P = Pred[⇒] P P
  
  Pred[⇐$]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Pred (Event Label) ℓzero) → Set
  Pred[⇐$]² P = Pred[⇐$] P P
  
  Pred[$⇒]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Pred (Event Label) ℓzero) → Set
  Pred[$⇒]² P = Pred[$⇒] P P
  
  Pred[⇐]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Pred (Event Label) ℓzero) → Set
  Pred[⇐]² P = Pred[⇐] P P

  
  Rel[⇒] : Rel (Event LabelSrc) ℓzero → Rel (Event LabelDst) ℓzero → Set
  Rel[⇒] Rˢ Rᵗ =
    ∀ {x y}
    → (x∈src : x ∈ src-events)
    → (y∈src : y ∈ src-events)
    → Rˢ x y
      ------------------------------
    → Rᵗ (ev[⇒] x∈src) (ev[⇒] y∈src)
  
  Rel[⇐$] : Rel (Event LabelSrc) ℓzero → Rel (Event LabelDst) ℓzero → Set
  Rel[⇐$] Rˢ Rᵗ =
    ∀ {x y}
    → (x∈src : x ∈ src-events)
    → (y∈src : y ∈ src-events)
    → Rᵗ (ev[⇒] x∈src) (ev[⇒] y∈src)
      ------------------------------
    → Rˢ x y

  Rel[$⇒] : Rel (Event LabelSrc) ℓzero → Rel (Event LabelDst) ℓzero → Set
  Rel[$⇒] Rˢ Rᵗ =
    ∀ {x y}
    → (x∈dst : x ∈ events dst)
    → (y∈dst : y ∈ events dst)
    → Rˢ (ev[⇐] x∈dst) (ev[⇐] y∈dst)
      ------------------------------
    → Rᵗ x y
    
  Rel[⇐] : Rel (Event LabelSrc) ℓzero → Rel (Event LabelDst) ℓzero → Set
  Rel[⇐] Rˢ Rᵗ =
    ∀ {x y}
    → (x∈dst : x ∈ events dst)
    → (y∈dst : y ∈ events dst)
    → Rᵗ x y
      ------------------------------
    → Rˢ (ev[⇐] x∈dst) (ev[⇐] y∈dst)
    
  Rel[⇒]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Rel (Event Label) ℓzero) → Set
  Rel[⇒]² R = Rel[⇒] R R
  
  Rel[⇐$]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Rel (Event Label) ℓzero) → Set
  Rel[⇐$]² R = Rel[⇐$] R R
  
  Rel[$⇒]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Rel (Event Label) ℓzero) → Set
  Rel[$⇒]² R = Rel[$⇒] R R
  
  Rel[⇐]² : (∀ {Label : Set} {{_ : LabelClass Label}} → Rel (Event Label) ℓzero) → Set
  Rel[⇐]² R = Rel[⇐] R R


  -- # Mapping Combinators

  [$⇒]→₁[⇒] :
      {Pˢ : Pred (Event LabelSrc) ℓzero}
    → {Pᵗ : Pred (Event LabelDst) ℓzero}
    → Pred[$⇒] Pˢ Pᵗ
      --------------
    → Pred[⇒] Pˢ Pᵗ
  [$⇒]→₁[⇒] {Pˢ} P[$⇒] x∈src Pxˢ =
    let x∈dst = events[⇒] x∈src
    in P[$⇒] x∈dst (subst Pˢ (ev[⇒⇐] x∈src) Pxˢ)

  [⇐]→₁[⇐$] :
      {Pˢ : Pred (Event LabelSrc) ℓzero}
    → {Pᵗ : Pred (Event LabelDst) ℓzero}
    → Pred[⇐] Pˢ Pᵗ
      --------------
    → Pred[⇐$] Pˢ Pᵗ
  [⇐]→₁[⇐$] {Pˢ} P[⇐] x∈src Pxᵗ =
    let x∈dst = events[⇒] x∈src
    in subst Pˢ (≡-sym (ev[⇒⇐] x∈src)) (P[⇐] x∈dst Pxᵗ)

  [⇐$]→₁[⇐] :
      {Pˢ : Pred (Event LabelSrc) ℓzero}
    → {Pᵗ : Pred (Event LabelDst) ℓzero}
    → Pred[⇐$] Pˢ Pᵗ
      --------------
    → Pred[⇐] Pˢ Pᵗ
  [⇐$]→₁[⇐] P[⇐$] = P[⇐$] ∘ events[⇐]
    

  [$⇒]→₂[⇒] :
      {Rˢ : Rel (Event LabelSrc) ℓzero}
    → {Rᵗ : Rel (Event LabelDst) ℓzero}
    → Rel[$⇒] Rˢ Rᵗ
      -------------
    → Rel[⇒] Rˢ Rᵗ
  [$⇒]→₂[⇒] {Rˢ} {Rᵗ} R[$⇒] x∈src y∈src Rxyˢ =
    let x∈dst = events[⇒] x∈src
        y∈dst = events[⇒] y∈src
    in R[$⇒] x∈dst y∈dst (subst-rel Rˢ (ev[⇒⇐] x∈src) (ev[⇒⇐] y∈src) Rxyˢ)
    
  [⇐]→₂[⇐$] :
      {Rˢ : Rel (Event LabelSrc) ℓzero}
    → {Rᵗ : Rel (Event LabelDst) ℓzero}
    → Rel[⇐] Rˢ Rᵗ
      -------------
    → Rel[⇐$] Rˢ Rᵗ
  [⇐]→₂[⇐$] {Rˢ} {Rᵗ} R[⇐] x∈src y∈src Rxyᵗ =
    let x∈dst = events[⇒] x∈src
        y∈dst = events[⇒] y∈src
    in subst-rel Rˢ (≡-sym (ev[⇒⇐] x∈src)) (≡-sym (ev[⇒⇐] y∈src)) (R[⇐] x∈dst y∈dst Rxyᵗ)

  [⇐$]→₂[⇐] :
      {Rˢ : Rel (Event LabelSrc) ℓzero}
    → {Rᵗ : Rel (Event LabelDst) ℓzero}
    → Rel[⇐$] Rˢ Rᵗ
      -------------
    → Rel[⇐] Rˢ Rᵗ
  [⇐$]→₂[⇐] R[⇐$] x∈dst y∈dst =
    R[⇐$] (events[⇐] x∈dst) (events[⇐] y∈dst)

  [⇒]→₂[$⇒] :
      {Rˢ : Rel (Event LabelSrc) ℓzero}
    → {Rᵗ : Rel (Event LabelDst) ℓzero}
    → Rel[⇒] Rˢ Rᵗ
      -------------
    → Rel[$⇒] Rˢ Rᵗ
  [⇒]→₂[$⇒] R[⇒] x∈dst y∈dst =
    R[⇒] (events[⇐] x∈dst) (events[⇐] y∈dst)
    

  ¬₁[⇒] :
      {Pˢ : Pred (Event LabelSrc) ℓzero}
    → {Pᵗ : Pred (Event LabelDst) ℓzero}
    → Pred[⇐$] Pˢ Pᵗ
      ----------------------
    → Pred[⇒] (¬₁ Pˢ) (¬₁ Pᵗ)
  ¬₁[⇒] P[⇐$] = contrapositive ∘ P[⇐$]
  
  ¬₁[⇐$] :
      {Pˢ : Pred (Event LabelSrc) ℓzero}
    → {Pᵗ : Pred (Event LabelDst) ℓzero}
    → Pred[⇒] Pˢ Pᵗ
      ----------------------
    → Pred[⇐$] (¬₁ Pˢ) (¬₁ Pᵗ)
  ¬₁[⇐$] P[⇒] = contrapositive ∘ P[⇒]
  
  
  ¬₂[⇒] :
      {Rˢ : Rel (Event LabelSrc) ℓzero}
    → {Rᵗ : Rel (Event LabelDst) ℓzero}
    → Rel[⇐$] Rˢ Rᵗ
      ----------------------
    → Rel[⇒] (¬₂ Rˢ) (¬₂ Rᵗ)
  ¬₂[⇒] R[⇐$] x∈src y∈src = contrapositive (R[⇐$] x∈src y∈src)


  ∩₂[⇒] :
      {Rˢ Qˢ : Rel (Event LabelSrc) ℓzero}
    → {Rᵗ Qᵗ : Rel (Event LabelDst) ℓzero}
    → Rel[⇒] Rˢ Rᵗ
    → Rel[⇒] Qˢ Qᵗ
      ----------------------------
    → Rel[⇒] (Rˢ ∩₂ Qˢ) (Rᵗ ∩₂ Qᵗ)
  ∩₂[⇒] R[⇒] Q[⇒] x∈src y∈src (Rˢxy , Qˢxy) =
    (R[⇒] x∈src y∈src Rˢxy , Q[⇒] x∈src y∈src Qˢxy)
    
  ∪₁[⇒] :
      {Pˢ Qˢ : Pred (Event LabelSrc) ℓzero}
    → {Pᵗ Qᵗ : Pred (Event LabelDst) ℓzero}
    → Pred[⇒] Pˢ Pᵗ
    → Pred[⇒] Qˢ Qᵗ
      -----------------------------
    → Pred[⇒] (Pˢ ∪₁ Qˢ) (Pᵗ ∪₁ Qᵗ)
  ∪₁[⇒] P[⇒] Q[⇒] x∈src (inj₁ Pˢx) = inj₁ (P[⇒] x∈src Pˢx)
  ∪₁[⇒] P[⇒] Q[⇒] x∈src (inj₂ Qˢx) = inj₂ (Q[⇒] x∈src Qˢx)
    
  ∪₂[⇐$] :
      {Rˢ Qˢ : Rel (Event LabelSrc) ℓzero}
    → {Rᵗ Qᵗ : Rel (Event LabelDst) ℓzero}
    → Rel[⇐$] Rˢ Rᵗ
    → Rel[⇐$] Qˢ Qᵗ
      -----------------------------
    → Rel[⇐$] (Rˢ ∪₂ Qˢ) (Rᵗ ∪₂ Qᵗ)
  ∪₂[⇐$] R[⇐$] Q[⇐$] x∈src y∈src (inj₁ Rᵗxy) = inj₁ (R[⇐$] x∈src y∈src Rᵗxy)
  ∪₂[⇐$] R[⇐$] Q[⇐$] x∈src y∈src (inj₂ Qᵗxy) = inj₂ (Q[⇐$] x∈src y∈src Qᵗxy)
  
  ×₂[⇐$] :
      {Pˢ Qˢ : Pred (Event LabelSrc) ℓzero}
    → {Pᵗ Qᵗ : Pred (Event LabelDst) ℓzero}
    → Pred[⇐$] Pˢ Pᵗ
    → Pred[⇐$] Qˢ Qᵗ
      -----------------------------
    → Rel[⇐$] (Pˢ ×₂ Qˢ) (Pᵗ ×₂ Qᵗ)
  ×₂[⇐$] P[⇐$] Q[⇐$] x∈src y∈src (Pᵗx , Qᵗy) =
    (P[⇐$] x∈src Pᵗx , Q[⇐$] y∈src Qᵗy)
    

  dom[⇐] : (R : Rel (Event LabelSrc) ℓzero) (Q : Rel (Event LabelDst) ℓzero)
    → (∀ {x} → x ∈ codom Q → x ∈ events dst)
    → Rel[⇐] R Q
      -----------------------
    → Pred[⇐] (dom R) (dom Q)
  dom[⇐] R Q Qʳ∈dst R[⇐]Q {x} x∈dst (y , Qxy) =
    let y∈dst = Qʳ∈dst (take-codom Q Qxy)
    in take-dom R (R[⇐]Q x∈dst y∈dst Qxy)
    
  codom[⇐] : (R : Rel (Event LabelSrc) ℓzero) (Q : Rel (Event LabelDst) ℓzero)
    → (∀ {x} → x ∈ dom Q → x ∈ events dst)
    → Rel[⇐] R Q
      ---------------------------
    → Pred[⇐] (codom R) (codom Q)
  codom[⇐] R Q Qˡ∈dst R[⇐]Q {y} y∈dst (x , Qxy) =
    let x∈dst = Qˡ∈dst (take-dom Q Qxy)
    in take-codom R (R[⇐]Q x∈dst y∈dst Qxy)
    
  udr[⇐] : (R : Rel (Event LabelSrc) ℓzero) (Q : Rel (Event LabelDst) ℓzero)
    → (∀ {x} → x ∈ udr Q → x ∈ events dst)
    → Rel[⇐] R Q
      -----------------------
    → Pred[⇐] (udr R) (udr Q)
  udr[⇐] R Q udrQ∈dst R[⇐]Q {x} x∈dst (inj₁ x∈Qˡ) =
    inj₁ (dom[⇐] R Q (udrQ∈dst ∘ inj₂) R[⇐]Q x∈dst x∈Qˡ)
  udr[⇐] R Q udrQ∈dst R[⇐]Q {y} y∈dst (inj₂ y∈Qˡ) =
    inj₂ (codom[⇐] R Q (udrQ∈dst ∘ inj₁) R[⇐]Q y∈dst y∈Qˡ)

  _ˡ∈src : (R : Rel (Event LabelSrc) ℓzero) → Set
  _ˡ∈src R =
    ∀ {x y}
    → R x y
      --------------
    → x ∈ src-events
    
  _ʳ∈src : (R : Rel (Event LabelSrc) ℓzero) → Set
  _ʳ∈src R =
    ∀ {x y}
    → R x y
      --------------
    → y ∈ src-events
    
  udr[_]∈src : (R : Rel (Event LabelSrc) ℓzero) → Set
  udr[_]∈src R =
    ∀ {x}
    → x ∈ udr R
      ---------------
    → x ∈ src-events
    
  lr→udr : (R : Rel (Event LabelSrc) ℓzero)
    → R ˡ∈src
    → R ʳ∈src
      ------------------
    → udr[ R ]∈src
  lr→udr _ Rˡ∈src Rʳ∈src (inj₁ (_ , po[xy])) = Rˡ∈src po[xy]
  lr→udr _ Rˡ∈src Rʳ∈src (inj₂ (_ , po[yx])) = Rʳ∈src po[yx]

  ⁺[⇒]ˡ : {R : Rel (Event LabelSrc) ℓzero} {Q : Rel (Event LabelDst) ℓzero}
    → (∀ {x y : Event LabelSrc} → R x y → x ∈ src-events)
    → Rel[⇒] R Q
      ----------------------------------------
    → Rel[⇒] (TransClosure R) (TransClosure Q)
  ⁺[⇒]ˡ Rˡ∈src R[⇒]Q x∈src y∈src [ Rxy ] = [ R[⇒]Q x∈src y∈src Rxy ]
  ⁺[⇒]ˡ Rˡ∈src R[⇒]Q x∈src y∈src ( Rxz ∷ R⁺zy ) =
    let z∈src = ⁺-lift-predˡ Rˡ∈src R⁺zy
    in R[⇒]Q x∈src z∈src Rxz ∷ ⁺[⇒]ˡ Rˡ∈src R[⇒]Q z∈src y∈src R⁺zy

  ⁺[⇐]ˡ : {R : Rel (Event LabelSrc) ℓzero} {Q : Rel (Event LabelDst) ℓzero}
    → (∀ {x y : Event LabelDst} → Q x y → x ∈ events dst)
    → Rel[⇐] R Q
      ----------------------------------------
    → Rel[⇐] (TransClosure R) (TransClosure Q)
  ⁺[⇐]ˡ Qˡ∈src R[⇐]Q x∈dst y∈dst [ Qxy ] = [ R[⇐]Q x∈dst y∈dst Qxy ]
  ⁺[⇐]ˡ Qˡ∈src R[⇐]Q x∈dst y∈dst ( Qxz ∷ Q⁺zy ) =
    let z∈dst = ⁺-lift-predˡ Qˡ∈src Q⁺zy
    in R[⇐]Q x∈dst z∈dst Qxz ∷ ⁺[⇐]ˡ Qˡ∈src R[⇐]Q z∈dst y∈dst Q⁺zy

  imm[$⇒]ˡ : {R : Rel (Event LabelSrc) ℓzero} {Q : Rel (Event LabelDst) ℓzero}
    → (∀ {x y : Event LabelDst} → Q x y → x ∈ events dst)
    → Rel[⇐] R Q
    → Rel[$⇒] R Q
      -----------------------------------
    → Rel[$⇒] (immediate R) (immediate Q)
  imm[$⇒]ˡ {R} {Q} Qˡ∈dst R[⇐]Q R[$⇒]Q {x} {y} x∈dst y∈dst (Rxy , ¬∃z) =
    (R[$⇒]Q x∈dst y∈dst Rxy , ¬∃z')
    where
    ¬∃z' : ¬ (∃[ z ] Q x z × TransClosure Q z y)
    ¬∃z' (z , Qxz , Q⁺zy) =
      let z∈dst = ⁺-lift-predˡ Qˡ∈dst Q⁺zy
      in ¬∃z (ev[⇐] z∈dst , R[⇐]Q x∈dst z∈dst Qxz , ⁺[⇐]ˡ Qˡ∈dst R[⇐]Q z∈dst y∈dst Q⁺zy)

  imm[⇐$]ˡ : {R : Rel (Event LabelSrc) ℓzero} {Q : Rel (Event LabelDst) ℓzero}
    → (∀ {x y : Event LabelSrc} → R x y → x ∈ src-events)
    → Rel[⇒] R Q
    → Rel[⇐$] R Q
      -----------------------------------
    → Rel[⇐$] (immediate R) (immediate Q)
  imm[⇐$]ˡ {R} {Q} Rˡ∈src R[⇒]Q R[⇐$]Q {x} {y} x∈src y∈src (Qxy , ¬∃z) =
    R[⇐$]Q x∈src y∈src Qxy , ¬∃z'
    where
    ¬∃z' : ¬ (∃[ z ] R x z × TransClosure R z y)
    ¬∃z' (z , Rxz , R⁺zy) =
      let z∈src = ⁺-lift-predˡ Rˡ∈src R⁺zy
      in ¬∃z (ev[⇒] z∈src , R[⇒]Q x∈src z∈src Rxz , ⁺[⇒]ˡ Rˡ∈src R[⇒]Q z∈src y∈src R⁺zy)


  relˡ∈src : {R : Rel (Event LabelDst) ℓzero}
    → (Rˡ∈dst : ∀ {x y} → R x y → x ∈ events dst)
    → (Rʳ∈dst : ∀ {x y} → R x y → y ∈ events dst)
      -------------------------------------------
    → (src-rel Rˡ∈dst Rʳ∈dst) ˡ∈src
  relˡ∈src Rˡ∈dst _ (x-dst , _ , dst-R[xy] , refl , refl) =
    (x-dst , Rˡ∈dst dst-R[xy] , refl)
    
  relʳ∈src : {R : Rel (Event LabelDst) ℓzero}
    → (Rˡ∈dst : ∀ {x y} → R x y → x ∈ events dst)
    → (Rʳ∈dst : ∀ {x y} → R x y → y ∈ events dst)
      -------------------------------------------
    → (src-rel Rˡ∈dst Rʳ∈dst) ʳ∈src
  relʳ∈src _ Rʳ∈dst (x-dst , y-dst , dst-R[xy] , refl , refl) =
    (y-dst , Rʳ∈dst dst-R[xy] , refl)


  rmwˡ∈src : src-rmw ˡ∈src
  rmwˡ∈src = relˡ∈src (rmwˡ∈ex dst-wf) (rmwʳ∈ex dst-wf)

  rmwʳ∈src : src-rmw ʳ∈src
  rmwʳ∈src = relʳ∈src (rmwˡ∈ex dst-wf) (rmwʳ∈ex dst-wf)
  
  udr-rmw∈src : udr[ src-rmw ]∈src
  udr-rmw∈src = lr→udr src-rmw rmwˡ∈src rmwʳ∈src
  

record GeneralFramework : Set₁ where
  field
    ev[⇐]    : {x : Event LabelDst} → (x∈dst : x ∈ events dst) → Event LabelSrc
  
  -- This seems to work. Interesting..
  open Definitions ev[⇐] using (Pred[⇐]²; Pred[$⇒]²)

  field
    -- # Properties
    
    uid[⇐]   : {uid : UniqueId} → Pred[⇐]² (HasUid uid)
    uid[$⇒]  : {uid : UniqueId} → Pred[$⇒]² (HasUid uid)
    tid[⇐]   : {tid : ThreadId} → Pred[⇐]² (HasTid tid)
    tid[$⇒]  : {tid : ThreadId} → Pred[$⇒]² (HasTid tid)
    Init[⇐]  : Pred[⇐]² EvInit
    Init[$⇒] : Pred[$⇒]² EvInit


-- | Several wellformedness properties that can be derived from the general framework.
--
-- Also contains some definitions, but only those that strictly require the full
-- framework. (`Definitions` only requires `ev[⇐]`)
--
--
-- # Design Decision: Not WellFormed
--
-- Not all definitions in this module strictly pertain to WellFormedness. However, they
-- do all depend on the `GeneralFramework` (which `Definitions` above does not). Therefore,
-- we group all those definitions in this module.
module WellFormed (ψ : GeneralFramework) where

  open GeneralFramework ψ
  open Definitions ev[⇐]
  

  -- # Mapping

  -- ## Mapping: Primitives


  ev[$⇒]eq  : {x y : Event LabelDst}
    → (x∈dst : x ∈ events dst) (y∈dst : y ∈ events dst)
    → ev[⇐] x∈dst ≡ ev[⇐] y∈dst
      -----------------------------
    → x ≡ y
  ev[$⇒]eq {x} {y} x∈dst y∈dst x[⇐]≡y[⇐] =
    let x[⇐]-has-uid : HasUid (ev-uid x) (ev[⇐] x∈dst)
        x[⇐]-has-uid = uid[⇐] x∈dst (ev-has-uid x)
        y[⇐]-has-uid : HasUid (ev-uid x) (ev[⇐] y∈dst)
        y[⇐]-has-uid = subst (HasUid (ev-uid x)) x[⇐]≡y[⇐] x[⇐]-has-uid
        y-has-uid : HasUid (ev-uid x) y
        y-has-uid = uid[$⇒] y∈dst y[⇐]-has-uid
    in unique-ids dst-wf _ (ev-has-uid x , x∈dst) (y-has-uid , y∈dst)
    

  -- |
  --
  -- # Design Decision: No explicit equivalence proof
  --
  -- An alternative definition, more consistent with the others, is as follows:
  -- ```
  -- {x y} → x∈dst → y∈dst → x ≡ y → ev[⇐] x∈dst ≡ ev[⇐] y∈dst
  -- ```
  -- Instead, we elected to omit the explicit equivalence proof, which results in
  -- the current definition.
  ev[⇐]eq : {x : Event LabelDst}
    → (x∈dst₁ x∈dst₂ : x ∈ events dst)
      --------------------------------
    → ev[⇐] x∈dst₁ ≡ ev[⇐] x∈dst₂
  ev[⇐]eq {x} x∈dst₁ x∈dst₂ = cong ev[⇐] (events-unique dst-wf x x∈dst₁ x∈dst₂)


  ev[⇐$]eq : {x y : Event LabelSrc}
    → (x∈src : x ∈ src-events) (y∈src : y ∈ src-events)
    → ev[⇒] x∈src ≡ ev[⇒] y∈src
      -------------------------
    → x ≡ y
  ev[⇐$]eq (dst-x , x∈dst , refl) (dst-x , y∈dst , refl) refl = ev[⇐]eq x∈dst y∈dst


  -- | Starting with event `x` in the target: Mapping `x` to the source,
  -- then mapping the result to the target, gives `x` again.
  ev[⇐⇒] : {x : Event LabelDst}
    → (x∈dst : x ∈ events dst)
    → (x∈src : ev[⇐] {x} x∈dst ∈ src-events)
      --------------------------------------
    → x ≡ ev[⇒] x∈src
  ev[⇐⇒] x∈dst (y , y∈dst , ev[⇐]x≡ev[⇐]y) = ev[$⇒]eq x∈dst y∈dst ev[⇐]x≡ev[⇐]y


  -- ## Mapping: Predicates

  Init[⇒] : Pred[⇒]² EvInit
  Init[⇒] = [$⇒]→₁[⇒] Init[$⇒]

  Init[⇐$] : Pred[⇐$]² EvInit
  Init[⇐$] = [⇐]→₁[⇐$] Init[⇐]
  
  uid[⇒] : ∀ {uid : UniqueId} → Pred[⇒]² (HasUid uid)
  uid[⇒] = [$⇒]→₁[⇒] uid[$⇒]

  uid[⇐$] : ∀ {uid : UniqueId} → Pred[⇐$]² (HasUid uid)
  uid[⇐$] = [⇐]→₁[⇐$] uid[⇐]
  
  ¬uid[⇒] : {uid : UniqueId} → Pred[⇒]² (¬₁ HasUid uid)
  ¬uid[⇒] = ¬₁[⇒] uid[⇐$]

  ¬uid[⇐$] : ∀ {uid : UniqueId} → Pred[⇐$]² (¬₁ HasUid uid)
  ¬uid[⇐$] = ¬₁[⇐$] uid[⇒]
  
  ¬uid[⇐] : ∀ {uid : UniqueId} → Pred[⇐]² (¬₁ HasUid uid)
  ¬uid[⇐] = [⇐$]→₁[⇐] ¬uid[⇐$]

  tid[⇒] : ∀ {tid : ThreadId} → Pred[⇒]² (HasTid tid)
  tid[⇒] = [$⇒]→₁[⇒] tid[$⇒]

  tid[⇐$] : ∀ {tid : ThreadId} → Pred[⇐$]² (HasTid tid)
  tid[⇐$] = [⇐]→₁[⇐$] tid[⇐]


  -- ## Mapping: Relations

  -- | Forward mapping of trivially-mapped relations (see `src-rel`)
  rel[$⇒] : {R : Rel (Event LabelDst) ℓzero}
    → (Rˡ∈dst : ∀ {x y} → R x y → x ∈ events dst)
    → (Rʳ∈dst : ∀ {x y} → R x y → y ∈ events dst)
      -------------------------------------------
    → Rel[$⇒] (src-rel Rˡ∈dst Rʳ∈dst) R
  rel[$⇒] {R} Rˡ∈dst Rʳ∈dst x∈dst y∈dst (_ , _ , dst-R[xy] , p , q) =
    subst-rel R
      (ev[$⇒]eq (Rˡ∈dst dst-R[xy]) x∈dst (≡-sym p))
      (ev[$⇒]eq (Rʳ∈dst dst-R[xy]) y∈dst (≡-sym q))
      dst-R[xy]

  -- | Backward mapping of trivially-mapped relations (see `src-rel`)
  rel[⇐] : {R : Rel (Event LabelDst) ℓzero}
    → (Rˡ∈dst : ∀ {x y} → R x y → x ∈ events dst)
    → (Rʳ∈dst : ∀ {x y} → R x y → y ∈ events dst)
      -------------------------------------------
    → Rel[⇐] (src-rel Rˡ∈dst Rʳ∈dst) R
  rel[⇐] {R} Rˡ∈dst Rʳ∈dst {x} {y} x∈dst y∈dst R[xy] =
    ( x
    , y
    , R[xy]
    , ev[⇐]eq x∈dst (Rˡ∈dst R[xy])
    , ev[⇐]eq y∈dst (Rʳ∈dst R[xy])
    )


  rmw[$⇒] : Rel[$⇒] src-rmw (rmw dst)
  rmw[$⇒] = rel[$⇒] (rmwˡ∈ex dst-wf) (rmwʳ∈ex dst-wf)
  
  rmw[⇒] : Rel[⇒] src-rmw (rmw dst)
  rmw[⇒] = [$⇒]→₂[⇒] rmw[$⇒]

  rmw[⇐] : Rel[⇐] src-rmw (rmw dst)
  rmw[⇐] = rel[⇐] (rmwˡ∈ex dst-wf) (rmwʳ∈ex dst-wf)

  rmw[⇐$] : Rel[⇐$] src-rmw (rmw dst)
  rmw[⇐$] = [⇐]→₂[⇐$] rmw[⇐]


  rmwˡ[⇐$] : Pred[⇐$] (dom src-rmw) (dom (rmw dst))
  rmwˡ[⇐$] x∈src (y , rmw[xy]) =
    let y∈dst = rmwʳ∈ex dst-wf rmw[xy]
    in ev[⇐] y∈dst , rmw[⇐$] x∈src (events[⇐] y∈dst) rmw[xy]
    
  rmwˡ[⇒] : Pred[⇒] (dom src-rmw) (dom (rmw dst))
  rmwˡ[⇒] x∈src (y , rmw[xy]) =
    let y∈src = rmwʳ∈src rmw[xy]
    in ev[⇒] y∈src , rmw[⇒] x∈src y∈src rmw[xy]

  rmwʳ[⇒] : Pred[⇒] (codom src-rmw) (codom (rmw dst))
  rmwʳ[⇒] x∈src (y , rmw[yx]) =
    let y∈src = rmwˡ∈src rmw[yx]
    in ev[⇒] y∈src , rmw[⇒] y∈src x∈src rmw[yx]

  ¬rmwˡ[⇒] : Pred[⇒] (¬₁ dom src-rmw) (¬₁ dom (rmw dst))
  ¬rmwˡ[⇒] = ¬₁[⇒] rmwˡ[⇐$]
  
  ¬rmwˡ[⇐$] : Pred[⇐$] (¬₁ dom src-rmw) (¬₁ dom (rmw dst))
  ¬rmwˡ[⇐$] = ¬₁[⇐$] rmwˡ[⇒]
  

  -- ## Mapping: Derived Predicates

  ¬Init[⇒] : Pred[⇒]² (¬₁ EvInit)
  ¬Init[⇒] = contrapositive ∘ Init[⇐$]

  ¬Init[⇐$] : Pred[⇐$]² (¬₁ EvInit)
  ¬Init[⇐$] = contrapositive ∘ Init[⇒]

  suid[⇒] : Rel[⇒]² SameUid
  suid[⇒] x∈src y∈src (same-uid x-uid y-uid) =
    same-uid (uid[⇒] x∈src x-uid) (uid[⇒] y∈src y-uid)
    
  suid[⇐$] : Rel[⇐$]² SameUid
  suid[⇐$] x∈src y∈src (same-uid x-uid y-uid) =
    same-uid (uid[⇐$] x∈src x-uid) (uid[⇐$] y∈src y-uid)

  stid[⇒] : Rel[⇒]² SameTid
  stid[⇒] x∈src y∈src (same-tid x-tid y-tid) =
    same-tid (tid[⇒] x∈src x-tid) (tid[⇒] y∈src y-tid)

  stid[⇐$] : Rel[⇐$]² SameTid
  stid[⇐$] x∈src y∈src (same-tid x-tid y-tid) =
    same-tid (tid[⇐$] x∈src x-tid) (tid[⇐$] y∈src y-tid)

  init/tid[⇒] : ∀ {tid : ThreadId} → Pred[⇒]² (EvInit ∪₁ HasTid tid)
  init/tid[⇒] = ∪₁[⇒] Init[⇒] tid[⇒]
  
  init+e/stid[⇐$] : Rel[⇐$]² ( ( EvInit ×₂ EvE ) ∪₂ SameTid )
  init+e/stid[⇐$] = ∪₂[⇐$] (×₂[⇐$] Init[⇐$] e[⇐$]) stid[⇐$]
    where
    e[⇐$] : Pred[⇐$]² EvE
    e[⇐$] _ _ = ev-e _


  -- # WellFormed Fields
  
  src-unique-ids : (uid : UniqueId) → Unique₁ _≡_ (HasUid uid ∩₁ src-events)
  src-unique-ids uid (x-uid , x∈src) (y-uid , y∈src) =
    ev[⇐$]eq x∈src y∈src
      (unique-ids dst-wf uid
        (uid[⇒] x∈src x-uid , events[⇒] x∈src)
        (uid[⇒] y∈src y-uid , events[⇒] y∈src))

  src-events-unique : UniquePred src-events
  src-events-unique _ (x₁ , x₁∈dst , refl) ( x₂ ,  x₂∈dst , p) with ev[$⇒]eq x₁∈dst x₂∈dst p
  src-events-unique _ (x₁ , x₁∈dst , refl) ( x₂ ,  x₂∈dst , _)    | refl with events-unique dst-wf _ x₁∈dst x₂∈dst
  src-events-unique _ (x₁ , x₁∈dst , refl) (.x₁ , .x₁∈dst , refl) | refl | refl = refl

  src-events-uid-dec : (uid : UniqueId) → Dec (∃[ x ] (HasUid uid ∩₁ src-events) x)
  src-events-uid-dec uid with events-uid-dec dst-wf uid
  src-events-uid-dec uid | yes (y , y-uid , y∈dst) = yes (ev[⇐] y∈dst , uid[⇐] y∈dst y-uid , events[⇐] y∈dst)
  src-events-uid-dec uid | no  ¬∃x = no lemma
    where
    lemma : ¬ (∃[ x ] (HasUid uid ∩₁ src-events) x)
    lemma (x , x-uid , x∈src) = ¬∃x (ev[⇒] x∈src , uid[⇒] x∈src x-uid , events[⇒] x∈src)

  -- Helper. Copied from DerivedWellformed. Used by `src-rmwˡ-xm`
  src-events-dec : DecPred src-events
  src-events-dec x with src-events-uid-dec (ev-uid x)
  src-events-dec x | yes (y , y-uid-x , y∈src) with ev-eq-dec x y
  src-events-dec x | yes (.x , y-uid-x , y∈src) | yes refl = yes y∈src
  src-events-dec x | yes (y , y-uid-x , y∈src)  | no x≢y  =
    no λ{x∈src → x≢y (src-unique-ids (ev-uid x) (ev-has-uid x , x∈src) (y-uid-x , y∈src))}
  src-events-dec x | no ¬∃x = no (λ{x∈src → ¬∃x (x , ev-has-uid x , x∈src)})

  src-rmwˡ-dec : DecPred (dom (src-rmw))
  src-rmwˡ-dec x with src-events-dec x
  ... | no x∉src = no (λ{(y , rmw[xy]) → x∉src (rmwˡ∈src rmw[xy])})
  ... | yes x∈src with rmwˡ-dec dst-wf (ev[⇒] x∈src)
  ... | yes (y , rmw[xy]) =
          let y∈dst = rmwʳ∈ex dst-wf rmw[xy]
          in yes (ev[⇐] y∈dst , rmw[⇐$] x∈src (events[⇐] y∈dst) rmw[xy])
  ... | no x∉rmwˡ = no (¬rmwˡ[⇐$] x∈src x∉rmwˡ)
