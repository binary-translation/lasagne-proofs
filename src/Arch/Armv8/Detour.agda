{-# OPTIONS --safe #-}

-- | A detour for a `Obi` cycle in Armv8, which only goes through R/W events.
module Arch.Armv8.Detour where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_,_; proj₁; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Level using () renaming (zero to ℓzero)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _∷ʳ_; _++_)
-- Library imports
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.Armv8


open Event
open Execution
open WellFormed
open Armv8Execution


ObiDetour : {ex : Execution LabelArmv8} → Armv8Execution ex → Rel (Event LabelArmv8) ℓzero
ObiDetour a8 x y = Obi a8 x y × EvRW x × EvRW y


private
  -- | Every Obi cycle goes through at least one R/W event.
  --
  -- Every Obi-cycle switches threads through `Obs` (rfe/coe/fre),
  -- which is defined over R/W events.
  rotate : {ex : Execution LabelArmv8}
    → WellFormed ex
    → (a8 : Armv8Execution ex)
    → {x : Event LabelArmv8}
    → TransClosure (Obi a8) x x
      ---------------------------------------------
    → ∃[ z ] ( EvRW z × TransClosure (Obi a8) z z )
  rotate wf a8 [ obi[xx] ] = ⊥-elim (obi-irreflexive wf a8 refl obi[xx])
  rotate {ex} wf a8 ( obi[xy] ∷ obi⁺[yx]) =
    case step obi[xy] of
    λ{ (inj₁ x-rw) → _ , x-rw , obi[xy] ∷ obi⁺[yx]
     ; (inj₂ po[xy]) → steps po[xy] [ obi[xy] ] obi⁺[yx]
     }
    where
    step : ∀ {x y : Event LabelArmv8} → Obi a8 x y → EvRW x ⊎ po ex x y
    step (obi-init ((refl , x-init) ⨾[ _ ]⨾ po[xy])) = inj₁ (wₜ⇒rw (init⇒wₜ x-init))
    step (obi-obs (obs-rfe rfe[xy])) = inj₁ (w⇒rw (×₂-applyˡ (rf-w×r wf) (proj₁ rfe[xy])))
    step (obi-obs (obs-coe coe[xy])) = inj₁ (w⇒rw (×₂-applyˡ (co-w×w wf) (proj₁ coe[xy])))
    step (obi-obs (obs-fre fre[xy])) = inj₁ (r⇒rw (×₂-applyˡ (fr-r×w wf) (proj₁ fre[xy])))
    step (obi-dob dob[xy]) = inj₂ (dob⇒po wf a8 dob[xy])
    step (obi-aob aob[xy]) = inj₂ (aob⇒po wf aob[xy])
    step (obi-bob bob[xy]) = inj₂ (bob⇒po wf bob[xy])
    
    steps : ∀ {x y : Event LabelArmv8}
      → po ex x y
      → TransClosure (Obi a8) x y
      → TransClosure (Obi a8) y x
      → ∃[ z ] ( EvRW z × TransClosure (Obi a8) z z )
    steps po[xy] obi⁺[xy] [ obi[yz] ] with step obi[yz]
    ... | inj₁ y-rw   = _ , y-rw , (obi[yz] ∷ obi⁺[xy])
    ... | inj₂ po[yz] = ⊥-elim (po-irreflexive wf refl (po-trans wf po[xy] po[yz]))
    steps po[xy] obi⁺[xy] ( obi[yz] ∷ obi⁺[zx]) with step obi[yz]
    ... | inj₁ y-rw   = _ , y-rw , (obi[yz] ∷ (obi⁺[zx] ++ obi⁺[xy]))
    ... | inj₂ po[yz] = steps (po-trans wf po[xy] po[yz]) (obi⁺[xy] ∷ʳ obi[yz]) obi⁺[zx]


  -- | Extends every OBI chain until it reaches a R/W event.
  --
  -- Every OBI edge is either po-related, or an `Obs` (rfe/coe/fre), which is RW×RW anyway.
  -- Every po-related chain can thus be extended until it reaches an `Obs`. (or reaches the
  -- end of the chain, which is R/W by the `y-rw` argument).
  to-detour : ∀ {ex : Execution LabelArmv8}
    → (wf : WellFormed ex)
    → (a8 : Armv8Execution ex)
    → {x y : Event LabelArmv8}
    → EvRW x
    → EvRW y
    → TransClosure ( Obi a8 ) x y
      ---------------------------------
    → TransClosure ( ObiDetour a8 ) x y
  to-detour wf a8 x-rw y-rw [ obi[xy] ]   = [ obi[xy] , x-rw , y-rw ]
  to-detour {ex} wf a8 {x} {y} x-rw y-rw ( _∷_ {_} {z} (obi-init ((refl , x-init) ⨾[ _ ]⨾ po[xz])) obi⁺[zy]) =
    lemma po[xz] obi⁺[zy]
    where
    lemma : {z : Event LabelArmv8} → po ex x z → TransClosure ( Obi a8 ) z y → TransClosure ( ObiDetour a8 ) x y
    lemma po[xz] [ obi[zy] ] with obi⇒po/obs wf a8 obi[zy]
    ... | inj₁ po[zy] = [ obi-init ((refl , x-init) ⨾[ _ ]⨾ po-trans wf po[xz] po[zy]) , x-rw , y-rw ]
    ... | inj₂ obs[zy] =
      let z-rw = obsˡ-rw wf obs[zy]
      in (obi-init ((refl , x-init) ⨾[ _ ]⨾ po[xz]) , x-rw , z-rw) ∷ [ obi-obs obs[zy] , z-rw , y-rw ]
    lemma po[xz] ( obi[zv] ∷ obi⁺[vy] ) with obi⇒po/obs wf a8 obi[zv]
    ... | inj₁ po[zv]  = lemma (po-trans wf po[xz] po[zv]) obi⁺[vy]
    ... | inj₂ obs[zv] =
      let z-rw = obsˡ-rw wf obs[zv]
          v-rw = obsʳ-rw wf obs[zv]
      in (obi-init ((refl , x-init) ⨾[ _ ]⨾ po[xz]) , x-rw , z-rw) ∷ (obi-obs obs[zv] , z-rw , v-rw)
        ∷ to-detour wf a8 v-rw y-rw obi⁺[vy]
  to-detour wf a8 x-rw y-rw ( obi-obs obs[xz] ∷ obi⁺[zy]) =
    let z-rw = obsʳ-rw wf obs[xz]
    in (obi-obs obs[xz] , x-rw , z-rw) ∷ to-detour wf a8 z-rw y-rw obi⁺[zy]
  to-detour wf a8 x-rw y-rw ( obi-dob dob[xz] ∷ obi⁺[zy]) =
    let z-rw = dobʳ-rw wf a8 dob[xz]
    in (obi-dob dob[xz] , x-rw , z-rw) ∷ to-detour wf a8 z-rw y-rw obi⁺[zy]
  to-detour wf a8 x-rw y-rw ( obi-aob aob[xz] ∷ obi⁺[zy]) =
    let z-rw = aobʳ-rw wf aob[xz]
    in (obi-aob aob[xz] , x-rw , z-rw) ∷ to-detour wf a8 z-rw y-rw obi⁺[zy]
  to-detour {ex} wf a8 {x} {y} x-rw y-rw (obi-bob (bob-f (po[xv] ⨾[ v ]⨾ (refl , v-f) ⨾[ _ ]⨾ po[vz])) ∷ obi⁺[zy]) =
    lemma po[vz] obi⁺[zy]
    where
    lemma : {z : Event LabelArmv8} → po ex v z → TransClosure ( Obi a8 ) z y → TransClosure ( ObiDetour a8 ) x y
    lemma {z} po[vz] [ obi[zy] ] with obi⇒po/obs wf a8 obi[zy]
    ... | inj₁ po[zy]  = [ obi-bob (bob-f (po[xv] ⨾[ _ ]⨾ (refl , v-f) ⨾[ _ ]⨾ po-trans wf po[vz] po[zy])) , x-rw , y-rw ]
    ... | inj₂ obs[zy] =
      let z-rw = obsˡ-rw wf obs[zy]
          bob[xz] = bob-f (po[xv] ⨾[ _ ]⨾ (refl , v-f) ⨾[ _ ]⨾ po[vz])
      in (obi-bob bob[xz] , x-rw , z-rw) ∷ [ obi-obs obs[zy] , z-rw , y-rw ]
    lemma {z} po[vz] ( obi[zu] ∷ obi⁺[uy]) with obi⇒po/obs wf a8 obi[zu]
    ... | inj₁ po[zu]  = lemma (po-trans wf po[vz] po[zu]) obi⁺[uy]
    ... | inj₂ obs[zu] =
      let z-rw = obsˡ-rw wf obs[zu]
          u-rw = obsʳ-rw wf obs[zu]
          bob[xz] = bob-f (po[xv] ⨾[ _ ]⨾ (refl , v-f) ⨾[ _ ]⨾ po[vz])
      in (obi-bob bob[xz] , x-rw , z-rw) ∷ (obi-obs obs[zu] , z-rw , u-rw) ∷ to-detour wf a8 u-rw y-rw obi⁺[uy]
  to-detour wf a8 x-rw y-rw (obi-bob (bob-la ((refl , x-l) ⨾[ _ ]⨾ po[xv] ⨾[ _ ]⨾ (refl , v-a))) ∷ obi⁺[vy]) =
    let v-rw = r⇒rw (a⇒r v-a)
        bob[xv] = bob-la ((refl , x-l) ⨾[ _ ]⨾ po[xv] ⨾[ _ ]⨾ (refl , v-a))
    in (obi-bob bob[xv] , x-rw , v-rw) ∷ to-detour wf a8 v-rw y-rw obi⁺[vy]
  to-detour {ex} wf a8 {x} {y} x-rw y-rw (obi-bob (bob-fld ((refl , x-r) ⨾[ _ ]⨾ po[xv] ⨾[ v ]⨾ (refl , v-fld) ⨾[ _ ]⨾ po[vz])) ∷ obi⁺[zy]) =
    lemma po[vz] obi⁺[zy]
    where
    lemma : {z : Event LabelArmv8} → po ex v z → TransClosure ( Obi a8 ) z y → TransClosure ( ObiDetour a8 ) x y
    lemma po[vz] [ obi[zy] ] with obi⇒po/obs wf a8 obi[zy]
    ... | inj₁ po[zy]  =
      let po[vy] = po-trans wf po[vz] po[zy]
      in [ obi-bob (bob-fld ((refl , x-r) ⨾[ _ ]⨾ po[xv] ⨾[ _ ]⨾ (refl , v-fld) ⨾[ _ ]⨾ po[vy])) , x-rw , y-rw ]
    ... | inj₂ obs[zy] =
      let z-rw = obsˡ-rw wf obs[zy]
          u-rw = obsʳ-rw wf obs[zy]
          bob[xz] = bob-fld ((refl , x-r) ⨾[ _ ]⨾ po[xv] ⨾[ _ ]⨾ (refl , v-fld) ⨾[ _ ]⨾ po[vz])
      in (obi-bob bob[xz] , x-rw , z-rw) ∷ [ obi-obs obs[zy] , z-rw , u-rw ]
    lemma po[vz] ( obi[zu] ∷ obi⁺[uy] ) with obi⇒po/obs wf a8 obi[zu]
    ... | inj₁ po[zu] = lemma (po-trans wf po[vz] po[zu]) obi⁺[uy]
    ... | inj₂ obs[zu] =
      let z-rw = obsˡ-rw wf obs[zu]
          u-rw = obsʳ-rw wf obs[zu]
          bob[xz] = bob-fld ((refl , x-r) ⨾[ _ ]⨾ po[xv] ⨾[ _ ]⨾ (refl , v-fld) ⨾[ _ ]⨾ po[vz])
      in ( obi-bob bob[xz] , x-rw , z-rw ) ∷ (obi-obs obs[zu] , z-rw , u-rw) ∷ to-detour wf a8 u-rw y-rw obi⁺[uy]
  to-detour {ex} wf a8 {x} {y} x-rw y-rw (obi-bob (bob-acq ((refl , x-aq) ⨾[ x ]⨾ po[xz])) ∷ obi⁺[zy]) =
    lemma po[xz] obi⁺[zy]
    where
    lemma : {z : Event LabelArmv8} → po ex x z → TransClosure ( Obi a8 ) z y → TransClosure ( ObiDetour a8 ) x y
    lemma po[xz] [ obi[zy] ] with obi⇒po/obs wf a8 obi[zy]
    ... | inj₁ po[zy] = [ obi-bob (bob-acq ((refl , x-aq) ⨾[ _ ]⨾ po-trans wf po[xz] po[zy])) , x-rw , y-rw ]
    ... | inj₂ obs[zy] =
      let z-rw = obsˡ-rw wf obs[zy]
          bob[xz] = bob-acq ((refl , x-aq) ⨾[ _ ]⨾ po[xz])
      in ( obi-bob bob[xz] , x-rw , z-rw ) ∷ [ obi-obs obs[zy] , z-rw , y-rw ]
    lemma po[xz] ( obi[zv] ∷ obi⁺[zy] ) with obi⇒po/obs wf a8 obi[zv]
    ... | inj₁ po[zv] = lemma (po-trans wf po[xz] po[zv]) obi⁺[zy]
    ... | inj₂ obs[zv] =
      let z-rw = obsˡ-rw wf obs[zv]
          v-rw = obsʳ-rw wf obs[zv]
          bob[xz] = bob-acq ((refl , x-aq) ⨾[ x ]⨾ po[xz])
      in (obi-bob bob[xz] , x-rw , z-rw) ∷ (obi-obs obs[zv] , z-rw , v-rw) ∷ to-detour wf a8 v-rw y-rw obi⁺[zy]
  to-detour {ex} wf a8 {x} {y} x-rw y-rw (obi-bob (bob-fst ((refl , x-w) ⨾[ _ ]⨾ po[xv] ⨾[ v ]⨾ (refl , v-fst) ⨾[ _ ]⨾ po[vz] ⨾[ _ ]⨾ (refl , z-w))) ∷ obi⁺[zy]) =
    let bob[xz] = bob-fst ((refl , x-w) ⨾[ _ ]⨾ po[xv] ⨾[ v ]⨾ (refl , v-fst) ⨾[ _ ]⨾ po[vz] ⨾[ _ ]⨾ (refl , z-w))
    in (obi-bob bob[xz] , x-rw , w⇒rw z-w) ∷ to-detour wf a8 (w⇒rw z-w) y-rw obi⁺[zy]
  to-detour wf a8 x-rw y-rw (obi-bob (bob-l₁ (po[xz] ⨾[ _ ]⨾ (refl , z-l))) ∷ obi⁺[zy]) =
    let bob[xz] = bob-l₁ (po[xz] ⨾[ _ ]⨾ (refl , z-l))
        z-rw = w⇒rw (l⇒w z-l)
    in (obi-bob bob[xz] , x-rw , z-rw) ∷ to-detour wf a8 z-rw y-rw obi⁺[zy]
  to-detour wf a8 x-rw y-rw (obi-bob (bob-l₂ (po[xv] ⨾[ _ ]⨾ (refl , v-l) ⨾[ _ ]⨾ coi[vz])) ∷ obi⁺[zy]) =
    let bob[xz] = bob-l₂ (po[xv] ⨾[ _ ]⨾ (refl , v-l) ⨾[ _ ]⨾ coi[vz])
        z-rw = w⇒rw (×₂-applyʳ (co-w×w wf) (proj₁ coi[vz]))
    in (obi-bob bob[xz] , x-rw , z-rw) ∷ to-detour wf a8 z-rw y-rw obi⁺[zy]


-- | If there exists an OB (ordered before) cycle in Armv8, then there
-- exists a cycle that goes only between R/W events.
--
-- No cycle exists within a single thread. It always goes through multiple threads.
-- The only way to go to another thread is through `Obs` (rfe/coe/fre), which
-- is defined over R/W events. Any po-related `Obi` chain can be extended to reach those
-- `Obs` edges.
detour : {ex : Execution LabelArmv8}
  → WellFormed ex
  → (a8 : Armv8Execution ex)
  → {x : Event LabelArmv8}
  → TransClosure (Obi a8) x x
    --------------------------------------
  → ∃[ z ] TransClosure (ObiDetour a8) z z
detour wf a8 obi⁺[xx] =
  let (z , z-rw , obi⁺[zz]) = rotate wf a8 obi⁺[xx]
      obid⁺[zz] = to-detour wf a8 z-rw z-rw obi⁺[zz]
  in z , obid⁺[zz]
