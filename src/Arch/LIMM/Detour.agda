{-# OPTIONS --safe #-}

-- | A detour is an alternative path through an execution, which satisfies different desired properties.
-- This module defines a detour for LIMM's ghb-relation. The detour guarantees that individual relations
-- within the cycle only go through R/W events; Whereas the original path could go between fences as well.
module Arch.LIMM.Detour where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst) renaming (sym to ≡-sym)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_; _∷ʳ_)
-- Local library imports
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
open WellFormed
open IsLIMMConsistent


--
-- This module contains the following public components:
-- * OrdAlt - alternative definition of `Ord`
-- * GhbiAlt - alternative definition of `Ghbi`
-- * detour - converts from a `Ghbi` cycle to a `GhbiAlt` cycle
-- * Some other helpers
--


-- | This is an alternative definition of `Ord` (in `Arch.LIMM`).
--
-- The following changes are included:
-- * The `SC` fence rules (`po;SC` and `SC;po`) are combined into a single rule
--   (`po;SC;po`)
-- * All edges are guaranteed to go between two R/W events
data OrdAlt (ex : Execution LabelLIMM) (x y : Event LabelLIMM) : Set where
  ord-init      : ( ⦗ EvInit ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ )                     x y → OrdAlt ex x y
  ord-rm        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y
  ord-ww        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → OrdAlt ex x y
  ord-sc        : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvF₌ SC ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y

  ord-rmw-dom   : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ dom (rmw ex) ⦘ )   x y → OrdAlt ex x y
  ord-rmw-codom : ( ⦗ codom (rmw ex) ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y

  ord-w         : ( ⦗ EvRW ⦘ ⨾ po ex ⨾ ⦗ EvWₜ trmw ⦘ ) x y → OrdAlt ex x y
  ord-r         : ( ⦗ EvRₜ trmw ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → OrdAlt ex x y

data GhbiAlt (ex : Execution LabelLIMM) (x y : Event LabelLIMM) : Set where
  ghbi-ord : OrdAlt ex x y → GhbiAlt ex x y
  ghbi-rfe : rfe ex x y    → GhbiAlt ex x y
  ghbi-coe : coe ex x y    → GhbiAlt ex x y
  ghbi-fre : fre ex x y    → GhbiAlt ex x y


private
  -- | Rotate the cycle such that it starts at a R/W event.
  --
  -- Note that every `ghb` cycle contains at least one R/W event, as every cycle passes through
  -- multiple threads. The only way to switch threads is through either of rfe, coe, or fre.
  -- Those relations all relate R/W events.
  rotate : ∀ {ex : Execution LabelLIMM}
    → WellFormed ex
    → {x : Event LabelLIMM}
    → TransClosure ( Ghbi ex ) x x
      --------------------------------------------
    → ∃[ y ] TransClosure ( Ghbi ex ) y y × EvRW y
  rotate {ex} wf {x} [ ghbi[xx] ] = ⊥-elim (ghbi-irreflexive wf refl ghbi[xx])
  rotate {ex} wf {x} ghbi⁺[xx]@(ghbi-rfe rfe[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , w⇒rw (×₂-applyˡ (rfe-w×r wf) rfe[xy])
  rotate {ex} wf {x} ghbi⁺[xx]@(ghbi-coe coe[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , w⇒rw (×₂-applyˡ (coe-w×w wf) coe[xy])
  rotate {ex} wf {x} ghbi⁺[xx]@(ghbi-fre fre[xy] ∷ ghbi⁺[yx]) = x , ghbi⁺[xx] , r⇒rw (×₂-applyˡ (fre-r×w wf) fre[xy])
  rotate {ex} wf {x} (ghbi-ord ord[xy] ∷ ghbi⁺[yx]) = step [ ord[xy] ] ghbi⁺[yx]
    where
    step : {x y : Event LabelLIMM}
      → TransClosure (Ord ex) x y → TransClosure (Ghbi ex) y x → ∃[ z ] TransClosure (Ghbi ex) z z × EvRW z
    step ord⁺[xy] [ ghbi-ord ord[yx] ] =
      let po[xx] = ord⁺⇒po wf (ord⁺[xy] ∷ʳ ord[yx])
      in ⊥-elim (po-irreflexive wf refl po[xx])
    step {x} {y} ord⁺[xy] [ ghbi-rfe rfe[yx]@(rf[yx] , _) ] =
      x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-rfe rfe[yx] ] , r⇒rw (×₂-applyʳ (rf-w×r wf) rf[yx])
    step {x} {y} ord⁺[xy] [ ghbi-coe coe[yx]@(co[yx] , _) ] = 
      x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-coe coe[yx] ] , w⇒rw (×₂-applyʳ (co-w×w wf) co[yx])
    step {x} {y} ord⁺[xy] [ ghbi-fre fre[yx]@(fr[yx] , _) ] = 
      x , ⁺-map _ ghbi-ord ord⁺[xy] ++ [ ghbi-fre fre[yx] ] , w⇒rw (×₂-applyʳ (fr-r×w wf) fr[yx])
    step ord⁺[xy] (ghbi-ord ord[yw] ∷ ghbi⁺[wx]) =
      step (ord⁺[xy] ∷ʳ ord[yw]) ghbi⁺[wx]
    step {x} {y} ord⁺[xy] (ghbi-rfe rfe[yw]@(rf[yw] , _) ∷ ghbi⁺[wx]) =
      y , (ghbi-rfe rfe[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , w⇒rw (×₂-applyˡ (rf-w×r wf) rf[yw])
    step {x} {y} ord⁺[xy] (ghbi-coe coe[yw]@(co[yw] , _) ∷ ghbi⁺[wx]) =
      y , (ghbi-coe coe[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , w⇒rw (×₂-applyˡ (co-w×w wf) co[yw])
    step {x} {y} ord⁺[xy] (ghbi-fre fre[yw]@(fr[yw] , _) ∷ ghbi⁺[wx]) =
      y , (ghbi-fre fre[yw] ∷ ghbi⁺[wx] ++ (⁺-map (λ z → z) ghbi-ord ord⁺[xy])) , r⇒rw (×₂-applyˡ (fr-r×w wf) fr[yw])

  -- Internal helper. Subsequent `Ord` elements are chained together, such that both ends
  -- of the chain contains R/W events
  --
  -- `ord⁺⇒alt` (below) traverses the fields of the `chain-ord` constructor to produce
  -- a sequence of `OrdAlt` elements.
  data Chain (ex : Execution LabelLIMM) (x y : Event LabelLIMM) : Set where
    chain-ord : EvRW x → EvRW y → TransClosure (Ord ex) x y → Chain ex x y
    chain-rfe : rfe ex x y → Chain ex x y
    chain-coe : coe ex x y → Chain ex x y
    chain-fre : fre ex x y → Chain ex x y

  to-chain : ∀ {ex : Execution LabelLIMM}
    → (wf : WellFormed ex)
    → {x y : Event LabelLIMM}
    → EvRW x
    → EvRW y
    → TransClosure ( Ghbi ex ) x y
      -----------------------------
    → TransClosure ( Chain ex ) x y
  to-chain wf {x} {y} x-rw y-rw [ ghbi-ord ord[xy] ] = [ chain-ord x-rw y-rw [ ord[xy] ] ]
  to-chain wf {x} {y} x-rw y-rw [ ghbi-rfe rfe[xy] ] = [ chain-rfe rfe[xy] ]
  to-chain wf {x} {y} x-rw y-rw [ ghbi-coe coe[xy] ] = [ chain-coe coe[xy] ]
  to-chain wf {x} {y} x-rw y-rw [ ghbi-fre fre[xy] ] = [ chain-fre fre[xy] ]
  to-chain wf {x} {y} x-rw y-rw (ghbi-rfe rfe[xz] ∷ ghbi⁺[zy]) = chain-rfe rfe[xz] ∷ to-chain wf (r⇒rw (×₂-applyʳ (rfe-w×r wf) rfe[xz])) y-rw ghbi⁺[zy]
  to-chain wf {x} {y} x-rw y-rw (ghbi-coe coe[xz] ∷ ghbi⁺[zy]) = chain-coe coe[xz] ∷ to-chain wf (w⇒rw (×₂-applyʳ (coe-w×w wf) coe[xz])) y-rw ghbi⁺[zy]
  to-chain wf {x} {y} x-rw y-rw (ghbi-fre fre[xz] ∷ ghbi⁺[zy]) = chain-fre fre[xz] ∷ to-chain wf (w⇒rw (×₂-applyʳ (fre-r×w wf) fre[xz])) y-rw ghbi⁺[zy]
  to-chain {ex} wf {x} {y} x-rw y-rw (ghbi-ord ord[xz] ∷ ghbi⁺[zy]) = step [ ord[xz] ] ghbi⁺[zy]
    where
    -- | `ord⁺[xz]` is the accumulator. `step` performs structural recursion on the second (explicit) argument.
    step : {z : Event LabelLIMM} → TransClosure (Ord ex) x z → TransClosure (Ghbi ex) z y → TransClosure (Chain ex) x y
    step ord⁺[xz] [ ghbi-ord ord[zy] ] = [ chain-ord x-rw y-rw ( ord⁺[xz] ∷ʳ ord[zy] ) ]
    step ord⁺[xz] [ ghbi-rfe rfe[zy] ] = chain-ord x-rw (w⇒rw (×₂-applyˡ (rfe-w×r wf) rfe[zy])) ord⁺[xz] ∷ [ chain-rfe rfe[zy] ]
    step ord⁺[xz] [ ghbi-coe coe[zy] ] = chain-ord x-rw (w⇒rw (×₂-applyˡ (coe-w×w wf) coe[zy])) ord⁺[xz] ∷ [ chain-coe coe[zy] ]
    step ord⁺[xz] [ ghbi-fre fre[zy] ] = chain-ord x-rw (r⇒rw (×₂-applyˡ (fre-r×w wf) fre[zy])) ord⁺[xz] ∷ [ chain-fre fre[zy] ]
    step ord⁺[xz] (ghbi-ord ord[zq] ∷ ghbi⁺[qy]) = step (ord⁺[xz] ∷ʳ ord[zq]) ghbi⁺[qy]
    step ord⁺[xz] (ghbi-rfe rfe[zq] ∷ ghbi⁺[qy]) =
      let (z-w , q-r) = ⊆₂-apply (rfe-w×r wf) rfe[zq]
      in chain-ord x-rw (w⇒rw z-w) ord⁺[xz] ∷ chain-rfe rfe[zq] ∷ to-chain wf (r⇒rw q-r) y-rw ghbi⁺[qy]
    step ord⁺[xz] (ghbi-coe coe[zq] ∷ ghbi⁺[qy]) =
      let (z-w , q-w) = ⊆₂-apply (coe-w×w wf) coe[zq]
      in chain-ord x-rw (w⇒rw z-w) ord⁺[xz] ∷ chain-coe coe[zq] ∷ to-chain wf (w⇒rw q-w) y-rw ghbi⁺[qy]
    step ord⁺[xz] (ghbi-fre fre[zq] ∷ ghbi⁺[qy]) =
      let (z-r , q-w) = ⊆₂-apply (fre-r×w wf) fre[zq]
      in chain-ord x-rw (r⇒rw z-r) ord⁺[xz] ∷ chain-fre fre[zq] ∷ to-chain wf (w⇒rw q-w) y-rw ghbi⁺[qy]

  ord⁺⇒alt : ∀ {ex : Execution LabelLIMM}
    → (wf : WellFormed ex)
    → {x y : Event LabelLIMM}
    → EvRW x
    → EvRW y
    → TransClosure (Ord ex) x y
      ----------------------------
    → TransClosure (OrdAlt ex) x y
  ord⁺⇒alt wf x-rw y-rw [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rm rm[xy] ] = [ ord-rm rm[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-ww ww[xy] ] = [ ord-ww ww[xy] ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rmw-dom (po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ] =
    [ ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-w (po[xz] ⨾[ z ]⨾ (refl , z-wₜ)) ] =
    [ ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-wₜ)) ]
  ord⁺⇒alt wf x-rw y-rw [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy]) ] =
    [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
        po[xy] = po-trans wf po[xz] po[zy]
    in [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-ww ww[xz] ∷ ord⁺[zy]) =
    ord-ww ww[xz] ∷ ord⁺⇒alt wf (w⇒rw (ord-predʳ ex ww[xz])) y-rw ord⁺[zy]
  ord⁺⇒alt {ex} wf x-rw y-rw (ord-rm rm[xz] ∷ ord⁺[zy]) =
    ord-rm rm[xz] ∷ ord⁺⇒alt wf (ord-predʳ ex rm[xz]) y-rw ord⁺[zy]
  ord⁺⇒alt wf x-rw y-rw (ord-sc₁ (po[xz] ⨾[ _ ]⨾ (refl , z-sc)) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
    in [ ord-sc ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw (ord-rmw-dom (po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ)) ∷ ord⁺[zy]) =
    ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ))
      ∷ ord⁺⇒alt wf (rₜ⇒rw (rmwˡ-r wf z∈rmwˡ)) y-rw ord⁺[zy]
  ord⁺⇒alt wf x-rw y-rw (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
        po[xy] = po-trans wf po[xz] po[zy]
    in [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  ord⁺⇒alt wf x-rw y-rw (ord-w (po[xz] ⨾[ _ ]⨾ (refl , z-w)) ∷ ord⁺[zy]) =
    ord-w ((refl , x-rw) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-w)) ∷ ord⁺⇒alt wf (wₜ⇒rw z-w) y-rw ord⁺[zy]
  ord⁺⇒alt wf x-rw y-rw (ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) =
    let po[zy] = ord⁺⇒po wf ord⁺[zy]
        po[xy] = po-trans wf po[xz] po[zy]
    in [ ord-r ((refl , x-rₜ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw)) ]
  -- Impossible cases
  ord⁺⇒alt wf x-rw y-rw [ ord-sc₁ (po[xy] ⨾[ _ ]⨾ (refl , y-sc)) ] = ⊥-elim (disjoint-f/rw _ (f₌⇒f y-sc , y-rw))
  ord⁺⇒alt wf x-rw y-rw [ ord-sc₂ ((refl , x-sc) ⨾[ _ ]⨾ po[xy]) ] = ⊥-elim (disjoint-f/rw _ (f₌⇒f x-sc , x-rw))
  ord⁺⇒alt wf x-rw y-rw (ord-sc₂ ((refl , x-sc) ⨾[ _ ]⨾ po[xz]) ∷ ord⁺[zy]) = ⊥-elim (disjoint-f/rw _ (f₌⇒f x-sc , x-rw))

  chain⇒alt⁺ : ∀ {ex : Execution LabelLIMM}
    → WellFormed ex
    → {x y : Event LabelLIMM}
    → Chain ex x y
      -----------------------------
    → TransClosure (GhbiAlt ex) x y
  chain⇒alt⁺ wf (chain-ord x-rw y-rw ord⁺[xy]) = ⁺-map _ ghbi-ord (ord⁺⇒alt wf x-rw y-rw ord⁺[xy])
  chain⇒alt⁺ wf (chain-rfe rfe[xy]) = [ ghbi-rfe rfe[xy] ]
  chain⇒alt⁺ wf (chain-coe coe[xy]) = [ ghbi-coe coe[xy] ]
  chain⇒alt⁺ wf (chain-fre fre[xy]) = [ ghbi-fre fre[xy] ]

  chain⁺⇒alt⁺ : ∀ {ex : Execution LabelLIMM}
    → WellFormed ex
    → {x y : Event LabelLIMM}
    → TransClosure (Chain ex) x y
      -----------------------------
    → TransClosure (GhbiAlt ex) x y
  chain⁺⇒alt⁺ wf = ⇔₂-apply-⊇₂ ⁺-idem ∘ ⁺-map _ (chain⇒alt⁺ wf)


-- | Converts a `Ghbi` /cycle/ into an alternative `GhbiAlt` cycle, which
-- contains only relations that go between read/write events.
--
-- Note that every ghbi-cycle goes between multiple threads. Moving to another thread
-- always goes through rfe/coe/fre; which are all between read/write events.
detour : ∀ {ex : Execution LabelLIMM}
  → WellFormed ex
  → {x : Event LabelLIMM}
  → TransClosure ( Ghbi ex ) x x
    --------------------------------------
  → ∃[ y ] TransClosure ( GhbiAlt ex ) y y
detour {ex} wf {x} ghbi⁺[xx] = 
  let (y , ghbi⁺[yy] , y-rw) = rotate wf ghbi⁺[xx]
      chain⁺[yy] = to-chain wf y-rw y-rw ghbi⁺[yy]
  in y , chain⁺⇒alt⁺ wf chain⁺[yy]


OrdAlt⇒Ord⁺ : {ex : Execution LabelLIMM} {x y : Event LabelLIMM}
  → OrdAlt ex x y
    -------------------------
  → TransClosure (Ord ex) x y
OrdAlt⇒Ord⁺ (ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) =
  [ ord-init ((refl , ev-init) ⨾[ _ ]⨾ po[xy]) ]
OrdAlt⇒Ord⁺ (ord-rm rm[xy]) = [ ord-rm rm[xy] ]
OrdAlt⇒Ord⁺ (ord-ww ww[xy]) = [ ord-ww ww[xy] ]
OrdAlt⇒Ord⁺ (ord-sc ((refl , x-rw) ⨾[ x ]⨾ po[xz] ⨾[ z ]⨾ (refl , z-sc) ⨾[ _ ]⨾ po[zy] ⨾[ y ]⨾ (refl , y-rw))) =
  ord-sc₁ (po[xz] ⨾[ z ]⨾ (refl , z-sc)) ∷ [ ord-sc₂ ((refl , z-sc) ⨾[ z ]⨾ po[zy]) ]
OrdAlt⇒Ord⁺ (ord-rmw-dom ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y∈rmwˡ))) =
  [ ord-rmw-dom (po[xy] ⨾[ y ]⨾ (refl , y∈rmwˡ)) ]
OrdAlt⇒Ord⁺ (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ x ]⨾ po[xy]) ]
OrdAlt⇒Ord⁺ (ord-w ((refl , x-rw) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-r))) =
  [ ord-w (po[xy] ⨾[ y ]⨾ (refl , y-r)) ]
OrdAlt⇒Ord⁺ (ord-r ((refl , x-r) ⨾[ x ]⨾ po[xy] ⨾[ y ]⨾ (refl , y-rw))) =
  [ ord-r ((refl , x-r) ⨾[ x ]⨾ po[xy]) ]


-- | Converts an alternative path to an original path
GhbiAlt⁺⇒Ghbi⁺ : ∀ {ex : Execution LabelLIMM}
  → {x y : Event LabelLIMM}
  → TransClosure (GhbiAlt ex) x y
    -----------------------------
  → TransClosure (Ghbi ex) x y
GhbiAlt⁺⇒Ghbi⁺ {ex} ghbi-alt⁺[xy] =
  ⁺-join (⁺-map _ step ghbi-alt⁺[xy])
  where
  step : ∀ {x y : Event LabelLIMM} → GhbiAlt ex x y → TransClosure (Ghbi ex) x y
  step (ghbi-ord ord[xy]) = ⁺-map _ ghbi-ord (OrdAlt⇒Ord⁺ ord[xy])
  step (ghbi-rfe rfe[xy]) = [ ghbi-rfe rfe[xy] ]
  step (ghbi-coe coe[xy]) = [ ghbi-coe coe[xy] ]
  step (ghbi-fre fre[xy]) = [ ghbi-fre fre[xy] ]


OrdAlt⇒po : ∀ {ex : Execution LabelLIMM}
  → WellFormed ex
  → {x y : Event LabelLIMM}
  → OrdAlt ex x y
    -------------
  → po ex x y
OrdAlt⇒po wf ord[xy] =
  let po⁺[xy] = ⁺-map id (ord⇒po wf) (OrdAlt⇒Ord⁺ ord[xy])
  in ⁺-join-trans (po-trans wf) po⁺[xy]


OrdAlt-irreflexive : ∀ {ex : Execution LabelLIMM} → WellFormed ex → Irreflexive _≡_ (OrdAlt ex)
OrdAlt-irreflexive wf refl = po-irreflexive wf refl ∘ OrdAlt⇒po wf

GhbiAlt-irreflexive : ∀ {ex : Execution LabelLIMM} → WellFormed ex → Irreflexive _≡_ (GhbiAlt ex)
GhbiAlt-irreflexive wf refl (ghbi-ord ord[xx]) = OrdAlt-irreflexive wf refl ord[xx]
GhbiAlt-irreflexive wf refl (ghbi-rfe rfe[xx]) = rf-irreflexive wf refl (proj₁ rfe[xx])
GhbiAlt-irreflexive wf refl (ghbi-coe coe[xx]) = co-irreflexive wf refl (proj₁ coe[xx])
GhbiAlt-irreflexive wf refl (ghbi-fre fre[xx]) = fr-irreflexive wf refl (proj₁ fre[xx])


-- # Helpers

OrdAltˡ∈ex : OrdAlt ˡ∈ex
OrdAltˡ∈ex wf = ⁺-lift-predˡ (poˡ∈ex wf ∘ (ord⇒po wf)) ∘ OrdAlt⇒Ord⁺

GhbiAltˡ∈ex : GhbiAlt ˡ∈ex
GhbiAltˡ∈ex wf (ghbi-ord ord[xy]) = OrdAltˡ∈ex wf ord[xy]
GhbiAltˡ∈ex wf (ghbi-rfe rfe[xy]) = rfˡ∈ex wf (proj₁ rfe[xy])
GhbiAltˡ∈ex wf (ghbi-coe coe[xy]) = coˡ∈ex wf (proj₁ coe[xy])
GhbiAltˡ∈ex wf (ghbi-fre fre[xy]) = frˡ∈ex wf (proj₁ fre[xy])


private
  ordfʳ+po :
      {ex : Execution LabelLIMM}
    → WellFormed ex
    → {P₁ P₂ : Pred (Event LabelLIMM) ℓzero}
    → {m : F-mode}
    → {x y z : Event LabelLIMM}
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) x y
    → po ex y z
    → P₂ z
      -----------------------------------------------------
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) x z
  ordfʳ+po wf ((refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qy] ⨾[ _ ]⨾ (refl , y-p₂)) po[yz] z-p₂ =
    let po[qz] = po-trans wf po[qy] po[yz]
    in (refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , z-p₂)


-- | Appends a `po` to the right of the `OrdAlt`, provided that both the `po`-segment
-- and the `OrdAlt`-segment end with a relaxed writes.
ordʳ+wᵣ : {ex : Execution LabelLIMM}
  → WellFormed ex
  → {x y z : Event LabelLIMM}
  → OrdAlt ex x y
  → po ex y z
  → EvW y
  → EvW z
    ----------------------------
  → TransClosure (OrdAlt ex) x z
ordʳ+wᵣ wf (ord-init ((refl , x-init) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _))) po[yz] y-w z-w =
  [ ord-init ((refl , x-init) ⨾[ _ ]⨾ po-trans wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-rm rm[xy]) po[yz] y-w z-w = [ ord-rm (ordfʳ+po wf rm[xy] po[yz] (w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-ww ww[xy]) po[yz] y-w z-w = [ ord-ww (ordfʳ+po wf ww[xy] po[yz] z-w) ]
ordʳ+wᵣ wf (ord-sc sc[xy]) po[yz] y-w z-w = [ ord-sc (ordfʳ+po wf sc[xy] po[yz] (w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) po[yz] y-w z-w =
  [ ord-rmw-codom ((refl , x∈rmwʳ) ⨾[ _ ]⨾ po-trans wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-w w[xy]@(_ ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ (refl , y-wₐ))) po[yz] y-w z-w =
  let y∈ex = poˡ∈ex wf po[yz]
      y∈rmwʳ = ⇔₁-apply-⊇₁ (rmw-w wf) (y∈ex , y-wₐ)
  in ord-w w[xy] ∷ [ ord-rmw-codom ((refl , y∈rmwʳ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
ordʳ+wᵣ wf (ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y-rw))) po[yz] y-w z-w =
  [ ord-r ((refl , x-rₐ) ⨾[ _ ]⨾ po-trans wf po[xy] po[yz] ⨾[ _ ]⨾ (refl , w⇒rw z-w)) ]
-- impossible cases
ordʳ+wᵣ wf (ord-rmw-dom ((refl , x-rw) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , y∈rmwˡ))) po[yz] y-w z-w =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r (rmwˡ-r wf y∈rmwˡ) , y-w))


private
  ordfˡ+po :
      {ex : Execution LabelLIMM}
    → WellFormed ex
    → {P₁ P₂ : Pred (Event LabelLIMM) ℓzero}
    → {m : F-mode}
    → {x y z : Event LabelLIMM}
    → po ex x y
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) y z
    → P₁ x
      -----------------------------------------------------
    → ( ⦗ P₁ ⦘  ⨾ po ex ⨾ ⦗ EvF₌ m ⦘ ⨾ po ex ⨾ ⦗ P₂ ⦘ ) x z
  ordfˡ+po wf po[xy] ((refl , y-p₁) ⨾[ _ ]⨾ po[yq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , y-p₂)) x-p₁ =
    let po[xq] = po-trans wf po[xy] po[yq]
    in (refl , x-p₁) ⨾[ _ ]⨾ po[xq] ⨾[ _ ]⨾ (refl , q-f) ⨾[ _ ]⨾ po[qz] ⨾[ _ ]⨾ (refl , y-p₂)


-- | Appends a `po` to the left of the `OrdAlt`, provided that both the `po`-segment
-- and the `OrdAlt`-segment start with a relaxed read.
ordˡ+rᵣ : {ex : Execution LabelLIMM}
  → WellFormed ex
  → {x y z : Event LabelLIMM}
  → po ex x y
  → OrdAlt ex y z
  → EvRᵣ y
  → EvRᵣ x
    -------------
  → OrdAlt ex x z
ordˡ+rᵣ wf po[xy] (ord-rm rm[yz]) y-rᵣ x-rᵣ = ord-rm (ordfˡ+po wf po[xy] rm[yz] (rₜ⇒r x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-sc sc[yz]) y-rᵣ x-rᵣ = ord-sc (ordfˡ+po wf po[xy] sc[yz] (rₜ⇒rw x-rᵣ))
ordˡ+rᵣ wf po[xy] (ord-rmw-dom ((refl , y-rw) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z∈rmwˡ))) y-rᵣ x-rᵣ =
  let po[xz] = po-trans wf po[xy] po[yz]
  in ord-rmw-dom ((refl , rₜ⇒rw x-rᵣ) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z∈rmwˡ))
ordˡ+rᵣ wf po[xy] (ord-w ((refl , y-rw) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-wₜ))) y-rᵣ x-rᵣ =
  let po[xz] = po-trans wf po[xy] po[yz]
  in ord-w ((refl , rₜ⇒rw x-rᵣ) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-wₜ))
-- impossible cases
ordˡ+rᵣ wf po[xy] (ord-init ((refl , y-init) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
  ⊥-elim (disjoint-r/init _ (rₜ⇒r y-rᵣ , y-init))
ordˡ+rᵣ {ex} wf po[xy] (ord-ww ww[yz]) y-rᵣ x-rᵣ = ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , ord-predˡ ex ww[yz]))
ordˡ+rᵣ wf po[xy] (ord-rmw-codom ((refl , y∈rmwʳ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
  ⊥-elim (disjoint-r/w _ (rₜ⇒r y-rᵣ , wₜ⇒w (rmwʳ-w wf y∈rmwʳ)))
ordˡ+rᵣ wf po[xy] (ord-r ((refl , y-rₐ) ⨾[ _ ]⨾ po[yz] ⨾[ _ ]⨾ (refl , z-rw))) y-rᵣ x-rᵣ =
  ⊥-elim (disjoint-rₜ _ (y-rᵣ , y-rₐ))


private
  -- Helpers for `¬ghbi-cycle₂`
  
  ghbi⇒po/sloc : {ex : Execution LabelLIMM}
    → WellFormed ex
    → {x y : Event LabelLIMM}
    → GhbiAlt ex x y
      ----------------------
    → (po ex ∪₂ SameLoc) x y
  ghbi⇒po/sloc wf (ghbi-ord ord[xy]) = inj₁ (OrdAlt⇒po wf ord[xy])
  ghbi⇒po/sloc wf (ghbi-rfe rfe[xy]) = inj₂ (⊆₂-apply (rf-sloc wf) (proj₁ rfe[xy]))
  ghbi⇒po/sloc wf (ghbi-coe coe[xy]) = inj₂ (⊆₂-apply (co-sloc wf) (proj₁ coe[xy]))
  ghbi⇒po/sloc wf (ghbi-fre fre[xy]) = inj₂ (⊆₂-apply (fr-sloc wf) (proj₁ fre[xy]))


  ghbi⇒coh : {ex : Execution LabelLIMM}
    → WellFormed ex
    → {x y : Event LabelLIMM}
    → SameLoc x y
    → GhbiAlt ex x y
      --------------
    → Coh ex x y
  ghbi⇒coh wf xy-sloc (ghbi-ord ord[xy]) = coh-po-loc (OrdAlt⇒po wf ord[xy] , xy-sloc)
  ghbi⇒coh wf _       (ghbi-rfe rfe[xy]) = coh-rf (proj₁ rfe[xy])
  ghbi⇒coh wf _       (ghbi-coe coe[xy]) = coh-co (proj₁ coe[xy])
  ghbi⇒coh wf _       (ghbi-fre fre[xy]) = coh-fr (proj₁ fre[xy])


-- | There exists no GHB cycle of length one
¬ghbi-cycle₁ : {ex : Execution LabelLIMM}
  → WellFormed ex
  → {x : Event LabelLIMM}
  → GhbiAlt ex x x
  → ⊥
¬ghbi-cycle₁ wf = GhbiAlt-irreflexive wf refl


-- | There exists no GHB cycle of length two
¬ghbi-cycle₂ : {ex : Execution LabelLIMM}
  → WellFormed ex
  → Acyclic _≡_ (Coh ex)
  → {x y : Event LabelLIMM}
  → GhbiAlt ex x y → GhbiAlt ex y x
  → ⊥
¬ghbi-cycle₂ wf coh ghbi[xy] ghbi[yx] with ghbi⇒po/sloc wf ghbi[yx]
¬ghbi-cycle₂ wf coh (ghbi-ord ord[xy]) _ | inj₁ po[yx]  =
  po-irreflexive wf refl (po-trans wf (OrdAlt⇒po wf ord[xy]) po[yx])
¬ghbi-cycle₂ wf coh (ghbi-rfe rfe[xy]) _ | inj₁ po[yx]  =
  let yx-sloc = sym-same-loc (⊆₂-apply (rf-sloc wf) (proj₁ rfe[xy]))
  in coh refl (coh-rf (proj₁ rfe[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
¬ghbi-cycle₂ wf coh (ghbi-coe coe[xy]) _ | inj₁ po[yx]  =
  let yx-sloc = sym-same-loc (⊆₂-apply (co-sloc wf) (proj₁ coe[xy]))
  in coh refl (coh-co (proj₁ coe[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
¬ghbi-cycle₂ wf coh (ghbi-fre fre[xy]) _ | inj₁ po[yx]  =
  let yx-sloc = sym-same-loc (⊆₂-apply (fr-sloc wf) (proj₁ fre[xy]))
  in coh refl (coh-fr (proj₁ fre[xy]) ∷ [ coh-po-loc (po[yx] , yx-sloc) ])
¬ghbi-cycle₂ wf coh ghbi[xy] ghbi[yx] | inj₂ yx-sloc =
  coh refl (ghbi⇒coh wf (sym-same-loc yx-sloc) ghbi[xy] ∷ [ ghbi⇒coh wf yx-sloc ghbi[yx] ])
