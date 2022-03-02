{-# OPTIONS --safe #-}

open import Arch.General.Execution using (Execution; WellFormed)
open import Arch.LIMM using (LabelLIMM)
open import MapArmv8toLIMM using (LIMM-Armv8Restricted)


module Proof.Mapping.Armv8toLIMM.Consistent
  (dst : Execution LabelLIMM)
  (dst-wf : WellFormed dst)
  (dst-ok : LIMM-Armv8Restricted dst)
  where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; subst)
open import Level using (Level) renaming (zero to ℓzero)
open import Function using (_∘_; id)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred; _∈_; _∉_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; _∷_; [_])
-- Library imports
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: General
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Execution
open import Arch.General.DerivedWellformed
open import Arch.General.Properties
open import Arch.LIMM as LIMM
open import Arch.Armv8 as Armv8
open import Arch.Armv8.Detour
-- Local imports: Theorem Specifications
open import MapArmv8toLIMM
-- Local imports: Proof Components
open import Proof.Mapping.Armv8toLIMM.Execution dst dst-wf dst-ok as PE
import Proof.Framework LabelArmv8 dst dst-wf as Ψ
import Proof.Mapping.Framework LabelArmv8 dst dst-wf as Δ


open Execution
open WellFormed
open IsLIMMConsistent
open LIMM-Armv8Restricted dst-ok
open PE.Extra



-- File structure
-- * Proof: Coherence
-- * Proof: Atomicity
-- * Proof: Global Order
-- * Result


-- General Framework
open Ψ.Definitions ev[⇐]
open Ψ.WellFormed ψ
-- Mapping-specific Framework
open Δ.Definitions δ
open Δ.WellFormed δ


private
  dst-consistent = consistent
  

-- # Proof: Coherence

src-ax-coherence : Acyclic _≡_ ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src )
src-ax-coherence refl coh[xx] =
  let x∈src = ⁺-lift-predˡ cohˡ∈src coh[xx]
  in ax-coherence dst-consistent refl (⁺[⇒]ˡ cohˡ∈src coh[⇒] x∈src x∈src coh[xx])
  where
  cohˡ∈src : ∀ {x y : Event LabelArmv8} → ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src ) x y → x ∈ events src
  cohˡ∈src (inj₁ (inj₁ (inj₁ po-loc[xy]))) = poˡ∈src (proj₁ po-loc[xy])
  cohˡ∈src (inj₁ (inj₁ (inj₂ rf[xy])))     = rfˡ∈src rf[xy]
  cohˡ∈src (inj₁ (inj₂ fr[xy]))            = frˡ∈src fr[xy]
  cohˡ∈src (inj₂ co[xy])                   = coˡ∈src co[xy]
  
  coh[⇒] : Rel[⇒] ( po-loc src ∪₂ rf src ∪₂ fr src ∪₂ co src ) (Coh dst)
  coh[⇒] x∈src y∈src (inj₁ (inj₁ (inj₁ po-loc[xy]))) = coh-po-loc (po-loc[⇒] x∈src y∈src po-loc[xy])
  coh[⇒] x∈src y∈src (inj₁ (inj₁ (inj₂ rf[xy])))     = coh-rf (rf[⇒] x∈src y∈src rf[xy])
  coh[⇒] x∈src y∈src (inj₁ (inj₂ fr[xy]))            = coh-fr (fr[⇒] x∈src y∈src fr[xy])
  coh[⇒] x∈src y∈src (inj₂ co[xy])                   = coh-co (co[⇒] x∈src y∈src co[xy])


-- # Proof: Atomicity

src-ax-atomicity : Empty₂ (rmw src ∩₂ (fre src ⨾ coe src))
src-ax-atomicity x y (rmw[xy] , (fre[xz] ⨾[ z ]⨾ coe[zy])) =
  let x∈src = rmwˡ∈src rmw[xy]
      y∈src = rmwʳ∈src rmw[xy]
      z∈src = coˡ∈src (proj₁ coe[zy])
  in
  ax-atomicity dst-consistent (ev[⇒] {x} x∈src) (ev[⇒] {y} y∈src)
    ( rmw[⇒] x∈src y∈src rmw[xy]
    , fre[⇒] x∈src z∈src fre[xz] ⨾[ _ ]⨾ coe[⇒] z∈src y∈src coe[zy]
    )


-- # Proof: Global Order

private
  empty-rel : {a : Level} {A : Set a} → Rel A ℓzero
  empty-rel _ _ = ⊥

-- |
--
-- We eliminate all Armv8 dependencies by inserting fences in LIMM.
src-a8 : Armv8Execution src
src-a8 =
  record
    { data₋ = empty-rel
    ; addr  = empty-rel
    ; ctrl  = empty-rel
      -- Armv8 specific relations
    ; data-def₁ = ⊆: (λ{_ _ ()})
    ; data-def₂ = ⊆: (λ{_ _ ()})
    ; addr-def₁ = ⊆: (λ{_ _ ()})
    ; addr-def₂ = ⊆: (λ{_ _ ()})
    ; ctrl-def₁ = ⊆: (λ{_ _ ()})
    ; ctrl-def₂ = ⊆: (λ{_ _ ()})
    ; ctrl-def₃ = ⊆: (λ{_ _ (() ⨾[ _ ]⨾ _)})
    }

src-ax-global-obs : Irreflexive _≡_ (Ob src-a8)
src-ax-global-obs refl ob[xx] =
  let (z , obd[zz]) = detour src-wf src-a8 ob[xx]
      z∈src = ⁺-lift-predˡ obidˡ∈src obd[zz]
      ghbi⁺⁺[zz] = ⁺[⇒]ˡ obidˡ∈src obi[⇒]ghbi z∈src z∈src obd[zz]
      ghbi⁺[zz] = ⁺-join ghbi⁺⁺[zz]
  in ax-global-ord dst-consistent refl ghbi⁺[zz]
  where
  obidˡ∈src : {x y : Event LabelArmv8} → ObiDetour src-a8 x y → x ∈ events src
  obidˡ∈src (obi[xy] , _ , _) = obiˡ∈ex src-wf src-a8 obi[xy]

  obs[⇒]ghbi : Rel[⇒] (Obs src) (Ghbi dst)
  obs[⇒]ghbi x∈src y∈src (obs-rfe rfe[xy]) = ghbi-rfe (rfe[⇒] x∈src y∈src rfe[xy])
  obs[⇒]ghbi x∈src y∈src (obs-coe coe[xy]) = ghbi-coe (coe[⇒] x∈src y∈src coe[xy])
  obs[⇒]ghbi x∈src y∈src (obs-fre fre[xy]) = ghbi-fre (fre[⇒] x∈src y∈src fre[xy])

  -- Because we eliminate the Armv8 dependencies in LIMM, no data-ordered-before
  -- relations can exist.
  ¬dob : {x y : Event LabelArmv8} → ¬ Dob src-a8 x y
  ¬dob (dob-ctrl (() ⨾[ _ ]⨾ _))
  ¬dob (dob-isb (inj₂ (() ⨾[ _ ]⨾ _) ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ _))
  ¬dob (dob-addr-po (() ⨾[ _ ]⨾ _ ⨾[ _ ]⨾ _))
  ¬dob (dob-coi ((inj₁ ()) ⨾[ _ ]⨾ _))
  ¬dob (dob-coi ((inj₂ ()) ⨾[ _ ]⨾ _))
  ¬dob (dob-rfi (inj₁ () ⨾[ _ ]⨾ _))
  ¬dob (dob-rfi (inj₂ () ⨾[ _ ]⨾ _))

  aob[⇒]ord : Rel[⇒] (Aob src) (Ord dst)
  aob[⇒]ord x∈src y∈src (aob-rmw rmw[xy]) =
    let po[xy] = proj₁ (⊆₂-apply (rmw-def src-wf) rmw[xy])
        xˢ-rₐ = rmwˡ-r src-wf (take-dom (rmw src) rmw[xy])
    in ord-r ((refl , Rₜ[⇒] x∈src xˢ-rₐ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])
  aob[⇒]ord x∈src y∈src (aob-rfi ((refl , x∈rmwʳ) ⨾[ _ ]⨾ rfi[xy] ⨾[ _ ]⨾ (refl , _))) =
    ord-rmw-codom ((refl , rmwʳ[⇒] x∈src x∈rmwʳ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src (proj₂ rfi[xy]))


  BobDetour : Rel (Event LabelArmv8) ℓzero
  BobDetour x y = Bob src x y × EvRW x × EvRW y

  aq⇒r : {x : Event LabelArmv8} → (EvA ∪₁ EvQ) x → EvR x
  aq⇒r (inj₁ x-a) = a⇒r x-a
  aq⇒r (inj₂ x-q) = q⇒r x-q


  bob[⇒]ord⁺ : Rel[⇒] BobDetour (TransClosure (Ord dst))
  bob[⇒]ord⁺ x∈src y∈src (bob-f (po[xz] ⨾[ _ ]⨾ (refl , zˢ-f) ⨾[ _ ]⨾ po[zy]) , _ , _) =
    let z∈src = poʳ∈ex src-wf po[xz]
        zᵗ-f = Ffull[⇒] z∈src zˢ-f
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]
    in ord-sc₁ (po[xz]ᵗ ⨾[ _ ]⨾ (refl , zᵗ-f)) ∷ [ ord-sc₂ ((refl , zᵗ-f) ⨾[ _ ]⨾ po[zy]ᵗ) ]
  bob[⇒]ord⁺ x∈src y∈src (bob-la ((refl , xˢ-l) ⨾[ xˢ ]⨾ po[xy]ˢ ⨾[ _ ]⨾ (refl , yˢ-a)) , _ , _)
    with l/tag xˢ-l
  ... | inj₁ xˢ-lᵣ =
    let xˢ-w = l⇒w xˢ-l
        xˢ-¬init = λ{xˢ-init → disjoint-init/l _ (xˢ-init , xˢ-l)}
        yˢ-r = a⇒r yˢ-a
        yᵗ-r = R[⇒] y∈src yˢ-r
        x∈dst = events[⇒] x∈src
        xᵗ-org-l = l-org x∈dst (subst (EvLₜ tmov) (ev[⇒⇐] x∈src) xˢ-lᵣ)
        (zᵗ , pi[xz]ᵗ , zᵗ-sc) = l-scʳ x∈dst xᵗ-org-l
        z≢y = λ{z≡y → disjoint-f/r _ (subst EvF z≡y (LIMM.f₌⇒f zᵗ-sc) , yᵗ-r)}
        po[zy]ᵗ = ⊥⊎-elim z≢y id (unsplit-poˡ dst-wf (¬Init[⇒] x∈src xˢ-¬init) (po[⇒] x∈src y∈src po[xy]ˢ) pi[xz]ᵗ)
    in ord-sc₁ (proj₁ pi[xz]ᵗ ⨾[ _ ]⨾ (refl , zᵗ-sc)) ∷ [ ord-sc₂ ((refl , zᵗ-sc) ⨾[ _ ]⨾ po[zy]ᵗ) ]
  ... | inj₂ xˢ-lₐ =
    let xˢ-wₐ = lₜ⇒wₜ xˢ-lₐ
        xᵗ-wₐ = Wₜ[⇒] x∈src xˢ-wₐ
        xᵗ∈rmwʳ = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (events[⇒] x∈src , xᵗ-wₐ)
    in [ ord-rmw-codom ((refl , xᵗ∈rmwʳ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]ˢ) ]
  bob[⇒]ord⁺ x∈src y∈src (bob-fld ((refl , xˢ-r) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , fld) ⨾[ _ ]⨾ po[zy]) , _ , y-rw)
    with r/tag xˢ-r
  ... | inj₁ xˢ-rᵣ =
    let po[xy]ˢ = po-trans src-wf po[xz] po[zy]
        (vᵗ , pi[xv]ᵗ , vᵗ-rm) = rᵣ-rmʳ (events[⇒] x∈src) (Rₜ[⇒] x∈src xˢ-rᵣ)
        vᵗ≢y = λ{vᵗ≡y → disjoint-f/rw _ (subst EvF vᵗ≡y (LIMM.f₌⇒f vᵗ-rm) , RW[⇒] y∈src y-rw)}
        po[xy]ᵗ = po[⇒] x∈src y∈src (po-trans src-wf po[xz] po[zy])
        xˢ-¬init = λ{xˢ-init → disjoint-r/init _ (xˢ-r , xˢ-init)}
        po[vy]ᵗ = ⊥⊎-elim vᵗ≢y id (unsplit-poˡ dst-wf (¬Init[⇒] x∈src xˢ-¬init) po[xy]ᵗ pi[xv]ᵗ)
    in [ ord-rm ((refl , R[⇒] x∈src xˢ-r) ⨾[ _ ]⨾ proj₁ pi[xv]ᵗ ⨾[ _ ]⨾ (refl , vᵗ-rm) ⨾[ _ ]⨾ po[vy]ᵗ ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw)) ]
  ... | inj₂ xˢ-rₐ =
    [ ord-r ((refl , Rₜ[⇒] x∈src xˢ-rₐ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src (po-trans src-wf po[xz] po[zy])) ]
  bob[⇒]ord⁺ {x} {y} x∈src y∈src (bob-acq ((refl , xˢ-aq) ⨾[ _ ]⨾ po[xy]ˢ) , _ , y-rw)
    with r/tag (aq⇒r xˢ-aq)
  ... | inj₁ xˢ-rᵣ =
    let (vᵗ , pi[xv]ᵗ , vᵗ-rm) = rᵣ-rmʳ (events[⇒] x∈src) (Rₜ[⇒] x∈src xˢ-rᵣ)
        ¬x-init = λ{x-init → disjoint-r/init _ (rₜ⇒r xˢ-rᵣ , x-init)}
        po[xy]ᵗ = po[⇒] x∈src y∈src po[xy]ˢ
        v≢y = λ{v≡y → disjoint-f/rw _ (subst EvF v≡y (LIMM.f₌⇒f vᵗ-rm) , RW[⇒] y∈src y-rw)}
        po[vy]ᵗ = ⊥⊎-elim v≢y id (unsplit-poˡ dst-wf (¬Init[⇒] x∈src ¬x-init) po[xy]ᵗ pi[xv]ᵗ)
    in [ ord-rm ((refl , R[⇒] x∈src (rₜ⇒r xˢ-rᵣ)) ⨾[ _ ]⨾ proj₁ pi[xv]ᵗ ⨾[ _ ]⨾ (refl , vᵗ-rm) ⨾[ _ ]⨾ po[vy]ᵗ ⨾[ _ ]⨾ (refl , RW[⇒] y∈src y-rw)) ]
  ... | inj₂ xˢ-rₐ =
    [ ord-r ((refl , Rₜ[⇒] x∈src xˢ-rₐ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]ˢ) ]
  bob[⇒]ord⁺ x∈src y∈src (bob-fst ((refl , x-w) ⨾[ _ ]⨾ po[xz]ˢ ⨾[ _ ]⨾ (refl , z-st) ⨾[ _ ]⨾ po[zy]ˢ ⨾[ _ ]⨾ (refl , y-w)) , _ , _) =
    let z∈src = poʳ∈src po[xz]ˢ
        po[xz]ᵗ = po[⇒] x∈src z∈src po[xz]ˢ
        po[zy]ᵗ = po[⇒] z∈src y∈src po[zy]ˢ
    in [ ord-ww ((refl , W[⇒] x∈src x-w) ⨾[ _ ]⨾ po[xz]ᵗ ⨾[ _ ]⨾ (refl , Fst[⇒] z∈src z-st) ⨾[ _ ]⨾ po[zy]ᵗ ⨾[ _ ]⨾ (refl , W[⇒] y∈src y-w)) ]
  bob[⇒]ord⁺ x∈src y∈src (bob-l₁ (po[xy] ⨾[ _ ]⨾ (refl , yˢ-l)) , x-rw , _)
    with l/tag yˢ-l
  ... | inj₁ yˢ-lᵣ =
    case rw/rw x-rw of
    λ{ (inj₁ x-r) →
         case r/tag x-r of
         λ{ (inj₁ x-rᵣ) →
              let x∈dst = events[⇒] x∈src
                  (z , pi[xz] , z-rm) = rᵣ-rmʳ x∈dst (Rₜ[⇒] x∈src x-rᵣ)
                  ¬x-init = λ{x-init → disjoint-r/init _ (rₜ⇒r x-rᵣ , x-init)}
                  yˢ-w = l⇒w yˢ-l
                  yᵗ-w = W[⇒] y∈src yˢ-w
                  z≢y = λ{z≡y → disjoint-f/w _ (subst EvF z≡y (LIMM.f₌⇒f z-rm) , yᵗ-w)}
                  po[zy] = ⊥⊎-elim z≢y id (unsplit-poˡ dst-wf (¬Init[⇒] x∈src ¬x-init) (po[⇒] x∈src y∈src po[xy]) pi[xz])
              in [ ord-rm ((refl , R[⇒] x∈src x-r) ⨾[ _ ]⨾ proj₁ pi[xz] ⨾[ _ ]⨾ (refl , z-rm) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , w⇒rw yᵗ-w)) ]
          ; (inj₂ x-rₐ) →
              [ ord-r ((refl , Rₜ[⇒] x∈src x-rₐ) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy]) ]
          }
     ; (inj₂ x-w) →
         let y∈dst = events[⇒] y∈src
             yᵗ-org-l = l-org y∈dst (subst (EvLₜ tmov) (ev[⇒⇐] y∈src) yˢ-lᵣ)
             (z , pi[zy] , z-ww) = l-wwˡ y∈dst yᵗ-org-l
             x≢z = λ{x≡z → disjoint-f/w _ (LIMM.f₌⇒f z-ww , subst EvW x≡z (W[⇒] x∈src x-w))}
             po[xz] = ⊥⊎-elim x≢z id (unsplit-poʳ dst-wf (po[⇒] x∈src y∈src po[xy]) pi[zy])
             xᵗ-w = W[⇒] x∈src x-w
             yᵗ-w = W[⇒] y∈src (wₜ⇒w (lₜ⇒wₜ yˢ-lᵣ))
         in [ ord-ww ((refl , xᵗ-w) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , z-ww) ⨾[ _ ]⨾ proj₁ pi[zy] ⨾[ _ ]⨾ (refl , yᵗ-w)) ]
     }
  ... | inj₂ y-lₐ =
    [ ord-w (po[⇒] x∈src y∈src po[xy] ⨾[ _ ]⨾ (refl , Wₜ[⇒] y∈src (lₜ⇒wₜ y-lₐ))) ]
  bob[⇒]ord⁺ x∈src y∈src (bob-l₂ (po[xz]ˢ ⨾[ _ ]⨾ (refl , zˢ-l) ⨾[ _ ]⨾ coi[zy]ˢ) , _ , y-rw)
    with l/tag zˢ-l
  ... | inj₁ zˢ-lᵣ =
    let z∈src = poʳ∈ex src-wf po[xz]ˢ
        z∈dst = events[⇒] z∈src
        zᵗ-org-l = l-org z∈dst (subst (EvLₜ tmov) (ev[⇒⇐] z∈src) zˢ-lᵣ)
        (vᵗ , pi[zv]ᵗ , vᵗ-sc) = l-scʳ z∈dst zᵗ-org-l
        po[xv]ᵗ = po-trans dst-wf (po[⇒] x∈src z∈src po[xz]ˢ) (proj₁ pi[zv]ᵗ)
        po[zy]ᵗ = po[⇒] z∈src y∈src (proj₂ coi[zy]ˢ)
        ¬z-init = λ{z-init → disjoint-init/l _ (Init[⇐$] z∈src z-init , zˢ-l)}
        v≢y : vᵗ ≢ ev[⇒] y∈src
        v≢y = λ{v≡y → disjoint-f/rw _ (subst EvF v≡y (LIMM.f₌⇒f vᵗ-sc) , RW[⇒] y∈src y-rw)}
        po[vy]ᵗ = ⊥⊎-elim v≢y id (unsplit-poˡ dst-wf ¬z-init po[zy]ᵗ pi[zv]ᵗ)
    in ord-sc₁ (po[xv]ᵗ ⨾[ _ ]⨾ (refl , vᵗ-sc)) ∷ [ ord-sc₂ ((refl , vᵗ-sc) ⨾[ _ ]⨾ po[vy]ᵗ) ]
  ... | inj₂ zˢ-lₐ =
    let zˢ-wₐ = lₜ⇒wₜ zˢ-lₐ
        z∈src = poʳ∈ex src-wf po[xz]ˢ
        zᵗ-wₐ = Wₜ[⇒] z∈src zˢ-wₐ
        zᵗ∈rmwʳ = ⇔₁-apply-⊇₁ (rmw-w dst-wf) (events[⇒] z∈src , zᵗ-wₐ)
        po[zy]ᵗ = po[⇒] z∈src y∈src (proj₂ coi[zy]ˢ)
    in ord-w (po[⇒] x∈src z∈src po[xz]ˢ ⨾[ _ ]⨾ (refl , zᵗ-wₐ)) ∷ [ ord-rmw-codom ((refl , zᵗ∈rmwʳ) ⨾[ _ ]⨾ po[zy]ᵗ) ]


  obi[⇒]ghbi : Rel[⇒] (ObiDetour src-a8) (TransClosure (Ghbi dst))
  obi[⇒]ghbi {x} {y} x∈src y∈src (obi-init ((refl , x-init) ⨾[ _ ]⨾ po[xy]) , _ , _) =
    [ ghbi-ord (ord-init ((refl , Init[⇒] x∈src x-init) ⨾[ _ ]⨾ po[⇒] x∈src y∈src po[xy])) ]
  obi[⇒]ghbi {x} {y} x∈src y∈src (obi-obs obs[xy] , _ , _) =
    [ obs[⇒]ghbi x∈src y∈src obs[xy] ]
  obi[⇒]ghbi {x} {y} x∈src y∈src (obi-dob dob[xy] , _ , _) = ⊥-elim (¬dob dob[xy])
  obi[⇒]ghbi {x} {y} x∈src y∈src (obi-aob aob[xy] , _ , _) = [ ghbi-ord (aob[⇒]ord x∈src y∈src aob[xy]) ]
  obi[⇒]ghbi {x} {y} x∈src y∈src (obi-bob bob[xy] , x-rw , y-rw) =
    ⁺-map id ghbi-ord (bob[⇒]ord⁺ x∈src y∈src (bob[xy] , x-rw , y-rw))
  

-- # Result

src-consistent : IsArmv8Consistent src
src-consistent =
  record
    { a8 = src-a8
      -- Armv8-specific consistency constraints
    ; ax-coherence  = src-ax-coherence
    ; ax-atomicity  = src-ax-atomicity
    ; ax-global-obs = src-ax-global-obs
    }
