{-# OPTIONS --safe #-}

module Arch.LIMM where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_)
open import Level using (Level; _⊔_) renaming (zero to ℓzero; suc to ℓsuc)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; proj₁; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Empty; _∈_)
open import Relation.Binary using (Rel; Irreflexive)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports: Helpers
open import Helpers
-- Local imports: Architectures
open import Arch.General.Event
open import Arch.General.Properties using (tag-eq-dec)
open import Arch.General.Execution
open import Arch.General.DerivedWellformed


open Event
open Execution
open WellFormed


data F-mode : Set where
  RM : F-mode
  WW : F-mode
  SC : F-mode


data LabelLIMM : Set where
  lab-r : Tag → Location → Value → LabelLIMM
  lab-w : Tag → Location → Value → LabelLIMM
  lab-f : F-mode → LabelLIMM


data LabR : LabelLIMM → Set where
  is-r : ∀ {tag : Tag} {loc : Location} → {val : Value} → LabR (lab-r tag loc val)


data LabW : LabelLIMM → Set where
  is-w : ∀ {tag : Tag} {loc : Location} {val : Value} → LabW (lab-w tag loc val)


data LabF : LabelLIMM → Set where
  is-f : ∀ {mode : F-mode} → LabF (lab-f mode)


-- # Lemmas/Properties

private
  labs-xopt : XOptPred₃ LabR LabW LabF
  labs-xopt (lab-r _ _ _) = xopt₁ is-r  (λ()) (λ())
  labs-xopt (lab-w _ _ _) = xopt₂ (λ()) is-w  (λ())
  labs-xopt (lab-f _)     = xopt₃ (λ()) (λ()) is-f

  r-unique : UniquePred LabR
  r-unique _ is-r is-r = refl

  w-unique : UniquePred LabW
  w-unique _ is-w is-w = refl

  f-unique : UniquePred LabF
  f-unique _ is-f is-f = refl

  r-tag : {lab : LabelLIMM} → LabR lab → Tag
  r-tag {lab-r tag _ _} is-r = tag

  w-tag : {lab : LabelLIMM} → LabW lab → Tag
  w-tag {lab-w tag _ _} is-w = tag

  r-loc : {lab : LabelLIMM} → LabR lab → Location
  r-loc {lab-r _ loc _} is-r = loc

  r-val : {lab : LabelLIMM} → LabR lab → Value
  r-val {lab-r _ _ val} is-r = val

  w-loc : {lab : LabelLIMM} → LabW lab → Location
  w-loc {lab-w _ loc _} is-w = loc

  w-val : {lab : LabelLIMM} → LabW lab → Value
  w-val {lab-w _ _ val} is-w = val

  fence-dec : DecRel (_≡_ {_} {F-mode})
  fence-dec WW  WW  = yes refl
  fence-dec RM  RM  = yes refl
  fence-dec SC  SC  = yes refl
  fence-dec WW  RM  = no (λ ())
  fence-dec WW  SC  = no (λ ())
  fence-dec RM  WW  = no (λ ())
  fence-dec RM  SC  = no (λ ())
  fence-dec SC  WW  = no (λ ())
  fence-dec SC  RM  = no (λ ())

  lab-eq-dec : DecRel (_≡_ {_} {LabelLIMM})
  lab-eq-dec (lab-r tag₁ loc₁ val₁) (lab-r tag₂ loc₂ val₂) =
    cong₃-dec lab-r (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-w tag₁ loc₁ val₁) (lab-w tag₂ loc₂ val₂) =
    cong₃-dec lab-w (λ{refl → refl}) (λ{refl → refl}) (λ{refl → refl}) (tag-eq-dec tag₁ tag₂) (ℕ-dec loc₁ loc₂) (ℕ-dec val₁ val₂)
  lab-eq-dec (lab-f m₁) (lab-f m₂) =
    cong-dec lab-f (λ{refl → refl}) (fence-dec m₁ m₂)
  -- Impossible cases
  lab-eq-dec (lab-r _ _ _) (lab-w _ _ _) = no (λ ())
  lab-eq-dec (lab-r _ _ _) (lab-f _)     = no (λ ())
  lab-eq-dec (lab-w _ _ _) (lab-r _ _ _) = no (λ ())
  lab-eq-dec (lab-w _ _ _) (lab-f _)     = no (λ ())
  lab-eq-dec (lab-f _)     (lab-r _ _ _) = no (λ ())
  lab-eq-dec (lab-f _)     (lab-w _ _ _) = no (λ ())


-- # LabelClass

instance
  LabelLIMM-ok : LabelClass LabelLIMM
  LabelLIMM-ok =
    record
      { labs-r        = LabR
      ; labs-w        = LabW
      ; labs-f        = LabF
      ; labs-xopt     = labs-xopt
      ; labs-r-unique = r-unique
      ; labs-w-unique = w-unique
      ; labs-f-unique = f-unique
      ; lab-r-tag     = r-tag
      ; lab-w-tag     = w-tag
      ; lab-r-loc     = r-loc
      ; lab-r-val     = r-val
      ; lab-w-loc     = w-loc
      ; lab-w-val     = w-val
      ; lab-eq-dec    = lab-eq-dec
      }

data EvR₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelLIMM → Set where
  ev-r₌ : {uid : UniqueId} {tid : ThreadId} → EvR₌ tag loc val (event uid tid (lab-r tag loc val))

data EvW₌ (tag : Tag) (loc : Location) (val : Value) : Event LabelLIMM → Set where
  ev-w₌ : {uid : UniqueId} {tid : ThreadId} → EvW₌ tag loc val (event uid tid (lab-w tag loc val))

data EvF₌ (mode : F-mode) : Event LabelLIMM → Set where
  ev-f₌ : {uid : UniqueId} {tid : ThreadId} → EvF₌ mode (event uid tid (lab-f mode))
  

-- | Events ordered across the program order (po).
--
--
-- # Design Decision: Not Union Representation
--
-- Consider this the union over all relations in it's constructors.
--
-- This data structure is much easier to handle than taking _∪₂_ over all these,
-- as constructing (or pattern-matching on) an instance looks like: inj₁ (inj₁ (inj₁ ...)))
data Ord (ex : Execution LabelLIMM) (x y : Event LabelLIMM) : Set where
  ord-init      : ( ⦗ EvInit ⦘ ⨾ po ex )                                x y → Ord ex x y
  ord-rm        : ( ⦗ EvR ⦘  ⨾ po ex ⨾ ⦗ EvF₌ RM ⦘ ⨾ po ex ⨾ ⦗ EvRW ⦘ ) x y → Ord ex x y
  ord-ww        : ( ⦗ EvW ⦘  ⨾ po ex ⨾ ⦗ EvF₌ WW ⦘ ⨾ po ex ⨾ ⦗ EvW ⦘ )  x y → Ord ex x y
  ord-sc₁       : ( po ex ⨾ ⦗ EvF₌ SC ⦘ )                               x y → Ord ex x y
  ord-sc₂       : ( ⦗ EvF₌ SC ⦘ ⨾ po ex )                               x y → Ord ex x y
  ord-rmw-dom   : ( po ex ⨾ ⦗ dom (rmw ex) ⦘ )                          x y → Ord ex x y
  ord-rmw-codom : ( ⦗ codom (rmw ex) ⦘ ⨾ po ex )                        x y → Ord ex x y
  ord-w         : ( po ex ⨾ ⦗ EvWₜ trmw ⦘ )                             x y → Ord ex x y
  ord-r         : ( ⦗ EvRₜ trmw ⦘ ⨾ po ex )                             x y → Ord ex x y

-- | Immediate global happens before.
data Ghbi (ex : Execution LabelLIMM) (x y : Event LabelLIMM) : Set where
  ghbi-ord : Ord ex x y → Ghbi ex x y
  ghbi-rfe : rfe ex x y → Ghbi ex x y
  ghbi-coe : coe ex x y → Ghbi ex x y
  ghbi-fre : fre ex x y → Ghbi ex x y

data Coh (ex : Execution LabelLIMM) (x y : Event LabelLIMM) : Set where
  coh-po-loc : po-loc ex x y → Coh ex x y
  coh-rf     : rf ex     x y → Coh ex x y
  coh-fr     : fr ex     x y → Coh ex x y
  coh-co     : co ex     x y → Coh ex x y

-- | Global happens before
ghb : Execution LabelLIMM → Rel (Event LabelLIMM) ℓzero
ghb ex = TransClosure (Ghbi ex)

record IsLIMMConsistent (ex : Execution LabelLIMM) : Set₁ where
  field
    ax-coherence  : Acyclic _≡_ (Coh ex)
    ax-atomicity  : Empty₂ (rmw ex ∩₂ (fre ex ⨾ coe ex))
    ax-global-ord : Irreflexive _≡_ (ghb ex)


-- # Helpers

f₌⇒f : {m : F-mode} {x : Event LabelLIMM} → EvF₌ m x → EvF x
f₌⇒f ev-f₌ = ev-f is-f

r₌⇒rₜ : {loc : Location} {val : Value} {x : Event LabelLIMM}
  → EvR₌ trmw loc val x → EvRₜ trmw x
r₌⇒rₜ ev-r₌ = ev-r is-r refl

w₌⇒wₜ : {loc : Location} {val : Value} {x : Event LabelLIMM}
  → EvW₌ trmw loc val x → EvWₜ trmw x
w₌⇒wₜ ev-w₌ = ev-w is-w refl


disjoint-f/mode : {m₁ m₂ : F-mode} → m₁ ≢ m₂ → Disjoint₁ (EvF₌ m₁) (EvF₌ m₂)
disjoint-f/mode m₁≢m₂ _ (ev-f₌ , ev-f₌) = ⊥-elim (m₁≢m₂ refl)

coh-irreflexive : {ex : Execution LabelLIMM} → (wf : WellFormed ex) → Irreflexive _≡_ (Coh ex)
coh-irreflexive wf refl (coh-po-loc (po[xx] , _)) = po-irreflexive wf refl po[xx]
coh-irreflexive wf refl (coh-rf rf[xx])           = rf-irreflexive wf refl rf[xx]
coh-irreflexive wf refl (coh-fr fr[xx])           = fr-irreflexive wf refl fr[xx]
coh-irreflexive wf refl (coh-co co[xx])           = co-irreflexive wf refl co[xx]

cohˡ∈ex : Coh ˡ∈ex
cohˡ∈ex wf (coh-po-loc po-loc[xy]) = poˡ∈ex wf (proj₁ po-loc[xy])
cohˡ∈ex wf (coh-rf rf[xy])         = rfˡ∈ex wf rf[xy]
cohˡ∈ex wf (coh-fr fr[xy])         = frˡ∈ex wf fr[xy]
cohˡ∈ex wf (coh-co co[xy])         = coˡ∈ex wf co[xy]


ord-f⇒po :
  ∀ {p₁ : Pred (Event LabelLIMM) ℓzero}
  → {f : F-mode}
  → {p₂ : Pred (Event LabelLIMM) ℓzero}
  → {ex : Execution LabelLIMM}
  → WellFormed ex
  → {x y : Event LabelLIMM}
  → (⦗ p₁ ⦘ ⨾ po ex ⨾ ⦗ EvF₌ f ⦘ ⨾ po ex ⨾ ⦗ p₂ ⦘) x y
  → po ex x y
ord-f⇒po wf ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) =
  po-trans wf po[xz] po[zy]


ord⇒po : {ex : Execution LabelLIMM} → (wf : WellFormed ex) → {x y : Event LabelLIMM} → Ord ex x y → po ex x y
ord⇒po wf (ord-init ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
ord⇒po wf (ord-rm ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[yx] ⨾[ _ ]⨾ (refl , _))) =
  po-trans wf po[xy] po[yx]
ord⇒po wf (ord-ww ((refl , _) ⨾[ _ ]⨾ po[xy] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[yx] ⨾[ _ ]⨾ (refl , _))) =
  po-trans wf po[xy] po[yx]
ord⇒po wf (ord-sc₁ (po[xy] ⨾[ _ ]⨾ (refl , _)))       = po[xy]
ord⇒po wf (ord-sc₂ ((refl , _) ⨾[ _ ]⨾ po[xy]))       = po[xy]
ord⇒po wf (ord-rmw-dom (po[xy] ⨾[ _ ]⨾ (refl , _)))   = po[xy]
ord⇒po wf (ord-rmw-codom ((refl , _) ⨾[ _ ]⨾ po[xy])) = po[xy]
ord⇒po wf (ord-w (po[xy] ⨾[ _ ]⨾ (refl , _)))         = po[xy]
ord⇒po wf (ord-r ((refl , _) ⨾[ _ ]⨾ po[xy]))         = po[xy]

ord⊆po : {ex : Execution LabelLIMM} → (wf : WellFormed ex) → Ord ex ⊆₂ po ex
ord⊆po wf = ⊆: (λ{_ _ → ord⇒po wf})

ord⁺⇒po : {ex : Execution LabelLIMM} → WellFormed ex → {x y : Event LabelLIMM}
  → TransClosure (Ord ex) x y → po ex x y
ord⁺⇒po {ex} wf = ⁺-join-trans (po-trans wf) ∘ (⁺-map (λ τ → τ) (ord⇒po wf))


-- | Helper. Avoids matching on the full composition expression everytime.
ord-predˡ : ∀ (ex : Execution LabelLIMM) {x y : Event LabelLIMM}
  → {P Q R : Pred (Event LabelLIMM) ℓzero}
  → ( ⦗ P ⦘ ⨾ po ex ⨾ ⦗ Q ⦘ ⨾ po ex ⨾ ⦗ R ⦘ ) x y
  → P x
ord-predˡ _ ((refl , Px) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , _)) = Px

-- | Helper. Avoids matching on the full composition expression everytime.
ord-predʳ : ∀ (ex : Execution LabelLIMM) {x y : Event LabelLIMM}
  → {P Q R : Pred (Event LabelLIMM) ℓzero}
  → ( ⦗ P ⦘ ⨾ po ex ⨾ ⦗ Q ⦘ ⨾ po ex ⨾ ⦗ R ⦘ ) x y
  → R y
ord-predʳ _ ((refl , _) ⨾[ _ ]⨾ po[xz] ⨾[ _ ]⨾ (refl , _) ⨾[ _ ]⨾ po[zy] ⨾[ _ ]⨾ (refl , Ry)) = Ry


ord-irreflexive : {ex : Execution LabelLIMM} → (wf : WellFormed ex) → Irreflexive _≡_ (Ord ex)
ord-irreflexive wf refl ord[xx] = po-irreflexive wf refl (ord⇒po wf ord[xx])

ghbi-irreflexive : {ex : Execution LabelLIMM} → (wf : WellFormed ex) → Irreflexive _≡_ (Ghbi ex)
ghbi-irreflexive wf refl (ghbi-ord ord[xx]) = ord-irreflexive wf refl ord[xx]
ghbi-irreflexive wf refl (ghbi-rfe rfe[xx]) = rf-irreflexive wf refl (proj₁ rfe[xx])
ghbi-irreflexive wf refl (ghbi-coe coe[xx]) = co-irreflexive wf refl (proj₁ coe[xx])
ghbi-irreflexive wf refl (ghbi-fre fre[xx]) = fr-irreflexive wf refl (proj₁ fre[xx])


ordˡ∈ex : Ord ˡ∈ex
ordˡ∈ex wf ord[xy] = poˡ∈ex wf (ord⇒po wf ord[xy])

ordʳ∈ex : Ord ʳ∈ex
ordʳ∈ex wf ord[xy] = poʳ∈ex wf (ord⇒po wf ord[xy])


ghbiˡ∈ex : Ghbi ˡ∈ex
ghbiˡ∈ex wf (ghbi-ord ord[xy]) = ordˡ∈ex wf ord[xy]
ghbiˡ∈ex wf (ghbi-rfe rfe[xy]) = rfˡ∈ex wf (proj₁ rfe[xy])
ghbiˡ∈ex wf (ghbi-coe coe[xy]) = coˡ∈ex wf (proj₁ coe[xy])
ghbiˡ∈ex wf (ghbi-fre fre[xy]) = frˡ∈ex wf (proj₁ fre[xy])

ghbiʳ∈ex : Ghbi ʳ∈ex
ghbiʳ∈ex wf (ghbi-ord ord[xy]) = ordʳ∈ex wf ord[xy]
ghbiʳ∈ex wf (ghbi-rfe rfe[xy]) = rfʳ∈ex wf (proj₁ rfe[xy])
ghbiʳ∈ex wf (ghbi-coe coe[xy]) = coʳ∈ex wf (proj₁ coe[xy])
ghbiʳ∈ex wf (ghbi-fre fre[xy]) = frʳ∈ex wf (proj₁ fre[xy])
