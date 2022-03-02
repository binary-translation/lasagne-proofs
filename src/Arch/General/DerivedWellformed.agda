{-# OPTIONS --safe #-}

module Arch.General.DerivedWellformed where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; subst; subst₂) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level) renaming (zero to ℓzero; suc to ℓsuc)
open import Function using (_∘_)
open import Data.Nat using (zero)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂; map₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum as S
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Rel; REL)
open import Relation.Binary using (IsStrictTotalOrder)
open import Relation.Binary renaming (IsStrictTotalOrder to STO)
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_; _++_; _∷ʳ_)
open import Function using (flip)
-- Local library imports
open import Dodo.Nullary
open import Dodo.Unary
open import Dodo.Binary
-- Local imports
open import Helpers
open import Arch.General.Event
open import Arch.General.Properties
open import Arch.General.Execution


open LabelClass {{...}}
open Execution
open WellFormed


module _ {Label : Set} {{_ : LabelClass Label}} where

  -- ## Type Aliases

  _ˡ∈ex : (R : Execution Label → Rel (Event Label) ℓzero) → Set₁
  _ˡ∈ex R =
      {ex : Execution Label}
    → WellFormed ex
    → {x y : Event Label}
    → R ex x y
      -------------------
    → x ∈ events ex


  _ʳ∈ex : (R : Execution Label → Rel (Event Label) ℓzero) → Set₁
  _ʳ∈ex R =
      {ex : Execution Label}
    → WellFormed ex
    → {x y : Event Label}
    → R ex x y
      -------------------
    → y ∈ events ex


  udr[_]∈ex : (R : Execution Label → Rel (Event Label) ℓzero) → Set₁
  udr[_]∈ex R =
      {ex : Execution Label}
    → WellFormed ex
    → {x : Event Label}
    → x ∈ udr (R ex)
      -----------------
    → x ∈ events ex


  private
    lr→udr : {R : Execution Label → Rel (Event Label) ℓzero}
      → R ˡ∈ex
      → R ʳ∈ex
        -----------
      → udr[ R ]∈ex
    lr→udr Rˡ∈ex Rʳ∈ex wf (inj₁ (_ , po[xy])) = Rˡ∈ex wf po[xy]
    lr→udr Rˡ∈ex Rʳ∈ex wf (inj₂ (_ , po[xy])) = Rʳ∈ex wf po[xy]


  -- ## Well-formedness Helpers: Events Membership

  poˡ∈ex : po ˡ∈ex
  poˡ∈ex {ex = ex} wf {_} {y} po[xy] =
    ⇔₁-apply-⊆₁ (po-elements wf) (take-udrˡ (po ex) po[xy])

  poʳ∈ex : po ʳ∈ex
  poʳ∈ex {ex = ex} wf {x} {_} po[xy] =
    ⇔₁-apply-⊆₁ (po-elements wf) (take-udrʳ (po ex) po[xy])

  po∈ex : udr[ po ]∈ex
  po∈ex = lr→udr poˡ∈ex poʳ∈ex

  piˡ∈ex : po-imm ˡ∈ex
  piˡ∈ex wf (po[xy] , _) = poˡ∈ex wf po[xy]

  piʳ∈ex : po-imm ʳ∈ex
  piʳ∈ex wf (po[xy] , _) = poʳ∈ex wf po[xy]

  coˡ∈ex : co ˡ∈ex
  coˡ∈ex wf {_} {y} co[xy] = ⊆₁-apply (co-elements wf) (inj₁ (y , co[xy]))

  coʳ∈ex : co ʳ∈ex
  coʳ∈ex wf {x} {_} co[xy] = ⊆₁-apply (co-elements wf) (inj₂ (x , co[xy]))

  rfˡ∈ex : rf ˡ∈ex
  rfˡ∈ex wf {_} {y} rf[xy] = ⊆₁-apply (rf-elements wf) (inj₁ (y , rf[xy]))

  rfʳ∈ex : rf ʳ∈ex
  rfʳ∈ex wf {x} {_} rf[xy] = ⊆₁-apply (rf-elements wf) (inj₂ (x , rf[xy]))

  frˡ∈ex : fr ˡ∈ex
  frˡ∈ex wf {_} {y} (rf[zx] ⨾[ z ]⨾ co[zy]) = rfʳ∈ex wf rf[zx]

  frʳ∈ex : fr ʳ∈ex
  frʳ∈ex wf {x} {_} (rf[zx] ⨾[ z ]⨾ co[zy]) = coʳ∈ex wf co[zy]

  rmwˡ∈ex : rmw ˡ∈ex
  rmwˡ∈ex wf {x} {y} rmw[xy] with ⊆₂-apply (rmw-def wf) rmw[xy]
  ... | (po[xy] , _) = ⇔₁-apply-⊆₁ (po-elements wf) (inj₁ (y , po[xy]))

  rmwʳ∈ex : rmw ʳ∈ex
  rmwʳ∈ex wf {x} {y} rmw[xy] with ⊆₂-apply (rmw-def wf) rmw[xy]
  ... | (po[xy] , _) = ⇔₁-apply-⊆₁ (po-elements wf) (inj₂ (x , po[xy]))

  rmwˡ-r : {ex : Execution Label}
    → WellFormed ex
    → {x : Event Label}
    → x ∈ dom (rmw ex)
      -----------------
    → EvRₜ trmw x
  rmwˡ-r wf (y , rmw[xy]) = ×₂-applyˡ (rmw-r×w wf) rmw[xy]

  rmwʳ-w : {ex : Execution Label}
    → WellFormed ex
    → {x : Event Label}
    → x ∈ codom (rmw ex)
      ------------------
    → EvWₜ trmw x
  rmwʳ-w wf (y , rmw[yx]) = ×₂-applyʳ (rmw-r×w wf) rmw[yx]


  -- ## Well-formedness: Relation (co-)domains

  pi-elements :
      {ex : Execution Label}
    → WellFormed ex
      ----------------------------
    → udr (po-imm ex) ⇔₁ events ex
  pi-elements {ex = ex} wf = ⇔₁-intro ⊆-proof ⊇-proof
    where
    ⊆-proof : udr (po-imm ex) ⊆₁ events ex
    ⊆-proof = ⊆₁-trans (udr-preserves-⊆ imm-⊆₂) (⇔₁-to-⊆₁ (po-elements wf))

    ⊇-proof : events ex ⊆₁ udr (po-imm ex)
    ⊇-proof = ⊆₁-trans (⇔₁-to-⊇₁ (po-elements wf)) (⇔₁-to-⊆₁ (splittable-imm-udr (po-splittable wf)))

  fr-elements :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → udr (fr ex) ⊆₁ events ex
  fr-elements {ex = ex} wf =
    begin⊆₁
      udr (fr ex)
    ⊆₁⟨ udr-preserves-⊆ (≡-to-⊆₂ refl) ⟩
      udr (flip (rf ex) ⨾ (co ex))
    ⊆₁⟨ udr-combine-⨾ ⟩
      udr (flip (rf ex)) ∪₁ udr (co ex)
    ⊆₁⟨ ⇔₁-to-⊆₁ (∪₁-substˡ (⇔₁-sym udr-flip)) ⟩
      udr (rf ex) ∪₁ udr (co ex)
    ⊆₁⟨ ∪₁-substˡ-⊆₁ (rf-elements wf) ⟩
      events ex ∪₁ udr (co ex)
    ⊆₁⟨ ∪₁-substʳ-⊆₁ (co-elements wf) ⟩
      events ex ∪₁ events ex
    ⊆₁⟨ ⇔₁-to-⊆₁ ∪₁-idem ⟩
      events ex
    ⊆₁∎
  
  -- | Derived definition of the (co-)domain of 'fr'.
  fr-r×w :
      {ex : Execution Label}
    → WellFormed ex
      -------------------
    → fr ex ⊆₂ EvR ×₂ EvW
  fr-r×w {ex = ex} wf = 
    begin⊆₂
      fr ex
    ⊆₂⟨ ⊆₂-refl ⟩
      flip (rf ex) ⨾ co ex
    ⊆₂⟨ ⨾-substʳ-⊆₂ (co-w×w wf) ⟩
      flip (rf ex) ⨾ ( EvW ×₂ EvW )
    ⊆₂⟨ ⨾-substˡ-⊆₂ (×₂-flip-⊆₂ (rf-w×r wf)) ⟩
      ( EvR ×₂ EvW ) ⨾ ( EvW ×₂ EvW )
    ⊆₂⟨ ×₂-combine-⨾ ⟩
      EvR ×₂ EvW
    ⊆₂∎

  fr-sloc :
      {ex : Execution Label}
    → WellFormed ex
      ----------------
    → fr ex ⊆₂ SameLoc
  fr-sloc {ex = ex} wf = 
    begin⊆₂
      fr ex
    ⊆₂⟨ ⊆₂-refl ⟩
      flip (rf ex) ⨾ co ex
    ⊆₂⟨ ⨾-substˡ-⊆₂ (flip-⊆₂ (rf-sloc wf)) ⟩
      flip SameLoc ⨾ co ex
    ⊆₂⟨ ⨾-substˡ-⊆₂ (flip-sym-⊆₂ sym-same-loc) ⟩
      SameLoc ⨾ co ex
    ⊆₂⟨ ⨾-substʳ-⊆₂ (co-sloc wf) ⟩
      SameLoc ⨾ SameLoc
    ⊆₂⟨ ⨾-trans-⊆₂ trans-same-loc ⟩
      SameLoc
    ⊆₂∎

  rfe-w×r :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → rfe ex ⊆₂ ( EvW ×₂ EvR )
  rfe-w×r {ex = ex} wf = ⊆₂-trans (external⊆ rf ex) (rf-w×r wf)

  coe-w×w :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → coe ex ⊆₂ ( EvW ×₂ EvW )
  coe-w×w {ex = ex} wf = ⊆₂-trans (external⊆ co ex) (co-w×w wf)

  fre-r×w :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → fre ex ⊆₂ ( EvR ×₂ EvW )
  fre-r×w {ex = ex} wf = ⊆₂-trans (external⊆ fr ex) (fr-r×w wf)

  rfi-w×r :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → rfi ex ⊆₂ ( EvW ×₂ EvR )
  rfi-w×r {ex = ex} wf = ⊆₂-trans (internal⊆ rf ex) (rf-w×r wf)

  coi-w×w :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → coi ex ⊆₂ ( EvW ×₂ EvW )
  coi-w×w {ex = ex} wf = ⊆₂-trans (internal⊆ co ex) (co-w×w wf)

  fri-r×w :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → fri ex ⊆₂ ( EvR ×₂ EvW )
  fri-r×w {ex = ex} wf = ⊆₂-trans (internal⊆ fr ex) (fr-r×w wf)


  -- ## Well-formedness: Derived `po` properties

  private

    po-shared-tid :
        { ex : Execution Label }
      → WellFormed ex
      → {x y : Event Label}
      → (po[xy] : po ex x y)
        --------------------------------------------------------------
      → ∃[ tid ] (EvInit x ⊎ HasTid tid x) × (EvInit y ⊎ HasTid tid y)
    po-shared-tid wf po[xy] with ⊆₂-apply (po-stid wf) po[xy]
    po-shared-tid wf {y = y} po[xy] | inj₁ (x-init , _) with ev-init/tid y
    po-shared-tid wf po[xy] | inj₁ (x-init , _) | xopt₁ y-init _ = zero , inj₁ x-init , inj₁ y-init
    po-shared-tid wf po[xy] | inj₁ (x-init , _) | xopt₂ _ (tid , y-tid) = tid , inj₁ x-init , inj₂ y-tid
    po-shared-tid wf po[xy] | inj₂ (same-tid {tid} x-tid y-tid) = tid , inj₂ x-tid , inj₂ y-tid


    po-shared-tid₂ :
        { ex : Execution Label }
      → WellFormed ex
      → {x y z : Event Label}
      → po ex x y → po ex y z
        ------------------------------------------------------------------------------------------
      → ∃[ tid ] (EvInit x ⊎ HasTid tid x) × (EvInit y ⊎ HasTid tid y) × (EvInit z ⊎ HasTid tid z)
    po-shared-tid₂ wf po[xy] po[yz] with po-shared-tid wf po[xy] | po-shared-tid wf po[yz]
    po-shared-tid₂ wf po[xy] po[yz] | _ , _ , inj₁ ev-init | tid₂ , inj₁ ev-init , z-init/tid =
      (tid₂ , inj₁ (po-init-first wf po[xy] ev-init) , inj₁ ev-init , z-init/tid)
    po-shared-tid₂ wf po[xy] po[yz] | tid₁ , x-init/tid₁ , inj₂ y-tid₁ | tid₂ , inj₂ y-tid₂ , inj₂ z-tid₂ =
      (tid₁ , x-init/tid₁ , inj₂ y-tid₁ , inj₂ (subst-tid (tid-unique y-tid₂ y-tid₁) z-tid₂))
    -- impossible
    po-shared-tid₂ wf {_} {y} po[xy] po[yz] | tid₁ , _ , inj₂ y-tid₁ | tid₂ , inj₁ y-init , _ =
      ⊥-elim (xopt₂-select₁ y-init (ev-init/tid y) (tid₁ , y-tid₁))
    po-shared-tid₂ wf {x} {y} {z} po[xy] po[yz] | tid₁ , fst , inj₂ y-tid₁ | tid₂ , inj₂ y-tid₂ , inj₁ z-init =
      absurd (po-init-first wf po[yz] z-init) (xopt₂-select₂ (tid₂ , y-tid₂) (ev-init/tid y))


    po-shared-tid₂' :
        { ex : Execution Label }
      → WellFormed ex
      → {x y z : Event Label}
      → po ex x z → po ex y z
        ------------------------------------------------------------------------------------------
      → ∃[ tid ] (EvInit x ⊎ HasTid tid x) × (EvInit y ⊎ HasTid tid y) × (EvInit z ⊎ HasTid tid z)
    po-shared-tid₂' {ex} wf {x} {y} {z} po[xz] po[yz] with xopt₂-sum (ev-init/tid z)
    ... | inj₁ z-init        = zero , inj₁ (po-init-first wf po[xz] z-init) , inj₁ (po-init-first wf po[yz] z-init) , inj₁ z-init
    ... | inj₂ (tid , z-tid) = tid , lemma z-tid po[xz] , lemma z-tid po[yz] , inj₂ z-tid
      where
      lemma : {tid : ThreadId} {x : Event Label} → HasTid tid z → po ex x z → (EvInit x ⊎ HasTid tid x)
      lemma z-tid po[xy] with ⊆₂-apply (po-stid wf) po[xy]
      ... | inj₁ (x-init , _) = inj₁ x-init
      ... | inj₂ xy-stid = inj₂ (subst-stid (sym-same-tid xy-stid) z-tid)


    lift∈ex :
        (ex : Execution Label)
      → (ev : Event Label)
      → (ev∈ex : ev ∈ events ex)
        -------------------------------------------------------
      → ∃[ tid ] WithPred ((EvInit ∪₁ HasTid tid) ∩₁ events ex)
    lift∈ex ex ev ev∈ex = map₂ (λ τ → with-pred ev (τ , ev∈ex)) (lemma ev)
      where
      -- This lemma is crucial; We should /not/ pattern-match on `ev` in the `lift∈ex` scope.
      -- Then Agda cannot infer that `ev∈ex` is included without explicitly
      -- pattern-matching.
      lemma : {Label : Set} {{_ : LabelClass Label}}
        → (ev : Event Label)
        → ∃[ tid ] (EvInit ∪₁ HasTid tid) ev
      lemma (event-init _ _ _) = zero , inj₁ ev-init
      lemma (event-skip _ tid) = tid  , inj₂ has-tid-skip
      lemma (event _ tid _)    = tid  , inj₂ has-tid


  po-same-tid :
      {ex : Execution Label}
    → WellFormed ex
    → {x y : Event Label}
    → {tid₁ tid₂ : ThreadId}
    → HasTid tid₁ x
    → HasTid tid₂ y
    → po ex x y
      -------------
    → tid₁ ≡ tid₂
  po-same-tid wf x-tid₁ y-tid₂ po[xy] with ⊆₂-apply (po-stid wf) po[xy]
  po-same-tid wf {x} {y} {tid₁} x-tid₁ y-tid₂ po[xy] | inj₁ (x-init , _) = ⊥-elim (xopt₂-select₁ x-init (ev-init/tid x) (tid₁ , x-tid₁))
  po-same-tid wf                x-tid₁ y-tid₂ po[xy] | inj₂ xy-sametid   = tid-unique (subst-stid xy-sametid x-tid₁) y-tid₂

  po-tidʳ : {Label : Set} {{_ : LabelClass Label}} {ex : Execution Label}
    → WellFormed ex
    → {x y : Event Label}
    → {tid : ThreadId}
    → po ex x y
    → HasTid tid x
      ------------
    → HasTid tid y
  po-tidʳ wf {x} {_} {tid} po[xy] x-tid with ⊆₂-apply (po-stid wf) po[xy]
  ... | inj₁ (x-init , _) = ⊥-elim (xopt₂-select₁ x-init (ev-init/tid x) (tid , x-tid))
  ... | inj₂ xy-stid = subst-stid xy-stid x-tid


  events-dec : {Label : Set} {{_ : LabelClass Label}}
    → {ex : Execution Label}
    → WellFormed ex
      -------------------
    → DecPred (events ex)
  events-dec {ex = ex} wf x with events-uid-dec wf (ev-uid x)
  events-dec {ex = ex} wf x | yes (y , y-uid-x , y∈dst) with ev-eq-dec x y
  events-dec {ex = ex} wf x | yes (.x , y-uid-x , y∈dst) | yes refl = yes y∈dst
  events-dec {ex = ex} wf x | yes (y , y-uid-x , y∈dst)  | no  x≢y  =
    no (λ{x∈dst → x≢y (unique-ids wf (ev-uid x) (ev-has-uid x , x∈dst) (y-uid-x , y∈dst))})
  events-dec {ex = ex} wf x | no ¬∃x = no (λ{x∈dst → ¬∃x (x , ev-has-uid x , x∈dst)})


  -- | For any `x` and `y` it is decidable whether `po x y` holds or not.
  po-dec : {ex : Execution Label}
    → WellFormed ex
      --------------
    → DecRel (po ex)
  po-dec wf x y with events-dec wf x | events-dec wf y
  po-dec wf x y | yes x∈ex | yes y∈ex with ev-init/tid x | ev-init/tid y
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ with po-tri wf zero (with-pred x (inj₁ x-init , x∈ex)) (with-pred y (inj₁ y-init , y∈ex))
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ | tri<  po[xy] _ _ = yes po[xy]
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ | tri≈ ¬po[xy] _ _ = no ¬po[xy]
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₁ y-init _ | tri> ¬po[xy] _ _ = no ¬po[xy]
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₂ _ (tid , y-tid) with po-tri wf tid (with-pred x (inj₁ x-init , x∈ex)) (with-pred y (inj₂ y-tid , y∈ex))
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₂ _ (tid , y-tid) | tri<  po[xy] _ _ = yes po[xy]
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₁ x-init _ | xopt₂ _ (tid , y-tid) | tri> ¬po[xy] _ _ = no ¬po[xy]
  po-dec {ex = ex} wf x y | yes x∈ex | yes y∈ex | xopt₂ x-¬init x-tid  | xopt₁ y-init _ = no (λ po[xy] → ⊤prec⊥-invert (po ex) (po-init-first wf) po[xy] x-¬init y-init)
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) with ℕ-dec tid₁ tid₂
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) | yes tid₁≡tid₂@refl with po-tri wf tid₁ (with-pred x (inj₂ x-tid₁ , x∈ex)) (with-pred y (inj₂ y-tid₂ , y∈ex))
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₁ , y-tid₂) | yes refl | tri<  po[xy] _ _ = yes po[xy]
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₁ , y-tid₂) | yes refl | tri≈ ¬po[xy] _ _ = no ¬po[xy]
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₁ , y-tid₂) | yes refl | tri> ¬po[xy] _ _ = no ¬po[xy]
  po-dec wf x y | yes x∈ex | yes y∈ex | xopt₂ _ (tid₁ , x-tid₁) | xopt₂ _ (tid₂ , y-tid₂) | no tid₁≢tid₂ = no (tid₁≢tid₂ ∘ po-same-tid wf x-tid₁ y-tid₂)
  po-dec wf x y | yes x∈ex | no y∉ex  = no (contrapositive (poʳ∈ex wf) y∉ex)
  po-dec wf x y | no  x∉ex | yes y∈ex = no (contrapositive (poˡ∈ex wf) x∉ex)
  po-dec wf x y | no  x∉ex | no y∉ex  = no (contrapositive (poˡ∈ex wf) x∉ex)


  po-trans :
      { ex : Execution Label }
    → WellFormed ex
      ------------------
    → Transitive (po ex)
  po-trans wf = splittable-trans (po-splittable wf)


  po-init-tri :
      {ex : Execution Label}
    → WellFormed ex
      -----------------------------------------------------------
    → Trichotomous _≡_ (filter-rel (EvInit ∩₁ events ex) (po ex))
  po-init-tri {ex = ex} wf (with-pred x (x-init , x∈ex)) (with-pred y (y-init , y∈ex))
    with po-tri wf zero (with-pred x (inj₁ x-init , x∈ex)) (with-pred y (inj₁ y-init , y∈ex))
  ... | tri<  a ¬b   ¬c = tri< a (λ{refl → ¬c a}) ¬c
  ... | tri≈ ¬a refl ¬c = tri≈ ¬a refl ¬c
  ... | tri> ¬a ¬b    c = tri> ¬a (λ{refl → ¬a c}) c


  po-thread-tri :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------------------------------------------------------------------
    → ∀ (tid : ThreadId) → Trichotomous _≡_ (filter-rel (HasTid tid ∩₁ events ex) (po ex))
  po-thread-tri {ex = ex} wf tid (with-pred x (x-tid , x∈ex)) (with-pred y (y-tid , y∈ex))
    with po-tri wf tid (with-pred x (inj₂ x-tid , x∈ex)) (with-pred y (inj₂ y-tid , y∈ex))
  ... | tri<  a ¬b   ¬c = tri< a (λ{refl → ¬b refl}) ¬c
  ... | tri≈ ¬a refl ¬c = tri≈ ¬a refl ¬c
  ... | tri> ¬a ¬b    c = tri> ¬a (λ{refl → ¬b refl}) c


  po-irreflexive :
      {ex : Execution Label}
    → WellFormed ex
      -----------------------
    → Irreflexive _≡_ (po ex)
  po-irreflexive {ex = ex} wf {x} refl po[xx] =
    let (tid , q) = lift∈ex ex x (poˡ∈ex wf po[xx])
    in tri-irreflexive (po-tri wf tid) {x = q} refl po[xx]

  po-acyclic :
      {ex : Execution Label}
    → WellFormed ex
      -------------------
    → Acyclic _≡_ (po ex)
  po-acyclic {ex = ex} wf {x} refl po⁺[xx] =
    let po[xx] = ⊆₂-apply (⁺-trans-⊆₂ (po-trans wf)) po⁺[xx]
    in po-irreflexive wf refl po[xx]


  -- ## Well-formedness: Derived `co` properties

  co-irreflexive :
      {ex : Execution Label}
    → WellFormed ex
      -----------------------
    → Irreflexive _≡_ (co ex)
  co-irreflexive {ex = ex} wf {x} refl co[xx] =
    let x-w = ×₂-applyˡ (co-w×w wf) co[xx]
        (loc , x-loc) = ⊆₁-apply W⊆SomeLoc x-w
    in tri-irreflexive (co-tri wf loc) {x = with-pred x (x-w , x-loc , coˡ∈ex wf co[xx])} refl co[xx]

  -- Coherence order is defined over same-location writes. Every location is initialised /exactly once/.
  co-unique-init :
      {uid₁ uid₂ : UniqueId} {loc₁ loc₂ : Location} {val₁ val₂ : Value}
    → {ex : Execution Label}
    → WellFormed ex
      ---------------------------------------------------------------
    → ¬ co ex (event-init uid₁ loc₁ val₁) (event-init uid₂ loc₂ val₂)
  co-unique-init {uid₁} {uid₂} {loc₁} {loc₂} {val₁} {val₂} {ex} wf co[xy] with ⊆₂-apply (co-sloc wf) co[xy]
  ... | same-loc has-loc-init has-loc-init
    with wf-init-≤1 wf loc₁
           (ev-init , has-loc-init , x∈evs)
           (ev-init , has-loc-init , y∈evs)
    where
    x∈evs = coˡ∈ex wf co[xy]
    y∈evs = coʳ∈ex wf co[xy]
  ... | refl = co-irreflexive wf refl co[xy]


  wf-init-co-≤1 :
      {ex : Execution Label}
    → WellFormed ex
      ----------------------------------------------------------------------
    → ∀ (loc : Location) → Unique₁ _≡_ (EvInit ∩₁ HasLoc loc ∩₁ udr (co ex))
  wf-init-co-≤1 wf loc (init-x , x-loc , x∈co) (init-y , y-loc , y∈co) =
    let x∈evs = ⊆₁-apply (co-elements wf) x∈co
        y∈evs = ⊆₁-apply (co-elements wf) y∈co
    in wf-init-≤1 wf loc (init-x , x-loc , x∈evs) (init-y , y-loc , y∈evs)


  -- ## Well-formedness: Derived `rf` properties

  rf-irreflexive :
      {ex : Execution Label}
    → WellFormed ex
      -----------------------
    → Irreflexive _≡_ (rf ex)
  rf-irreflexive {ex = ex} wf {x} refl rf[xx] =
    disjoint-r/w _ (×₂-applyʳ (rf-w×r wf) rf[xx] , ×₂-applyˡ (rf-w×r wf) rf[xx])


  -- ## Well-formedness: Derived `fr` properties

  fr-irreflexive :
      {ex : Execution Label}
    → WellFormed ex
      -----------------------
    → Irreflexive _≡_ (fr ex)
  fr-irreflexive {ex = ex} wf {x} refl fr[xx] =
    disjoint-r/w _ (×₂-applyˡ (fr-r×w wf) fr[xx] , ×₂-applyʳ (fr-r×w wf) fr[xx])


  -- ## Well-formedness: Derived internal/external properties

  -- | Law of excluded middle for internal/external relations
  internal⊎external :
      (R : Execution Label → Rel (Event Label) ℓzero)
    → {ex : Execution Label}
    → WellFormed ex
      -----------------------------------------------
    → R ex ⇔₂ internal R ex ∪₂ external R ex
  internal⊎external R {ex} wf = ⇔: ⊆-proof ⊇-proof
    where
    ⊆-proof : R ex ⊆₂' internal R ex ∪₂ external R ex
    ⊆-proof x y Rxy with po-dec wf x y
    ⊆-proof x y Rxy | yes po[xy] = inj₁ (Rxy , po[xy])
    ⊆-proof x y Rxy | no ¬po[xy] = inj₂ (Rxy , ¬po[xy])

    ⊇-proof : internal R ex ∪₂ external R ex ⊆₂' R ex
    ⊇-proof x y (inj₁ (Rxy , _)) = Rxy
    ⊇-proof x y (inj₂ (Rxy , _)) = Rxy


  po-thread-splittable :
      {ex : Execution Label}
    → WellFormed ex
      -----------------------------------------------------------------------------------
    → ∀ (tid : ThreadId) → SplittableOrder (filter-rel (HasTid tid ∩₁ events ex) (po ex))
  po-thread-splittable {ex = ex} wf tid = filter-splittableʳ (po-splittable wf) (HasTid tid ∩₁ events ex) lemma
    where
    lemma : {x y : Event Label} → (HasTid tid ∩₁ events ex) x → po ex x y → (HasTid tid ∩₁ events ex) y
    lemma (x-tid , x∈ex) po[xy] = (po-tidʳ wf po[xy] x-tid , poʳ∈ex wf po[xy])


  po-tidˡ :
      {ex : Execution Label}
    → WellFormed ex
    → {tid : ThreadId} {x y : Event Label}
    → HasTid tid y
    → po ex x y
      ------------------------
    → (EvInit ∪₁ HasTid tid) x
  po-tidˡ wf y-tid po[xy] with ⊆₂-apply (po-stid wf) po[xy]
  ... | inj₁ (x-init , _) = inj₁ x-init
  ... | inj₂ xy-stid      = inj₂ (subst-stid (sym-same-tid xy-stid) y-tid)


  po-ex-splittable :
      {ex : Execution Label}
    → WellFormed ex
      -----------------------------------------------------------------------------------------------
    → ∀ (tid : ThreadId) → SplittableOrder (filter-rel ((EvInit ∪₁ HasTid tid) ∩₁ events ex) (po ex))
  po-ex-splittable {ex = ex} wf tid =
    filter-splittableˡ (po-splittable wf) ((EvInit ∪₁ HasTid tid) ∩₁ events ex) po-init/tidˡ
    where
    po-init/tidˡ : {tid : ThreadId} {x y : Event Label} → ((EvInit ∪₁ HasTid tid) ∩₁ events ex) y → po ex x y → ((EvInit ∪₁ HasTid tid) ∩₁ events ex) x
    po-init/tidˡ (inj₁ y-init , y∈ex) po[xy] = (inj₁ (po-init-first wf po[xy] y-init) , poˡ∈ex wf po[xy])
    po-init/tidˡ (inj₂ y-tid , y∈ex)  po[xy] = (po-tidˡ wf y-tid po[xy] , poˡ∈ex wf po[xy])


  unsplit-poˡ :
      {ex : Execution Label}
    → WellFormed ex
    → {x y z : Event Label}
    → ¬ EvInit x
    → po ex x z → po-imm ex x y
      -------------------------
    → y ≡ z ⊎ po ex y z
  unsplit-poˡ {ex = ex} wf {x} {y} {z} x-¬init po[xz] pi[xy] =
    let (tid , x-tid) = xopt₂-elim₁ x-¬init (ev-init/tid x)
        y-tid = po-tidʳ wf (proj₁ pi[xy]) x-tid
        z-tid = po-tidʳ wf po[xz] x-tid
    in
    case unsplitˡ (po-thread-tri wf tid) (po-thread-splittable wf tid)
           {x = with-pred x (x-tid , poˡ∈ex wf po[xz])}
           {y = with-pred y (y-tid , piʳ∈ex wf pi[xy])}
           {z = with-pred z (z-tid , poʳ∈ex wf po[xz])}
           po[xz] (⊆₂-apply imm-filter-⊆₂ pi[xy]) of
    (S.map₁ with-pred-≡)


  unsplit-poʳ :
      {ex : Execution Label}
    → WellFormed ex
    → {x y z : Event Label}
    → po ex x z → po-imm ex y z
      -------------------------
    → x ≡ y ⊎ po ex x y
  unsplit-poʳ {ex} wf {x} {y} {z} po[xz] pi[yz] with po-shared-tid₂' wf po[xz] (proj₁ pi[yz])
  ... | tid , x-init/tid , y-init/tid , z-init/tid = 
    case unsplitʳ (po-tri wf tid) (po-ex-splittable wf tid)
           {x = with-pred x (x-init/tid , poˡ∈ex wf po[xz])}
           {y = with-pred y (y-init/tid , piˡ∈ex wf pi[yz])}
           {z = with-pred z (z-init/tid , poʳ∈ex wf po[xz])}
           po[xz] (⊆₂-apply imm-filter-⊆₂ pi[yz]) of
    S.map₁ with-pred-≡


  private
    unique-po-pred :
        {ex : Execution Label}
      → WellFormed ex
      → {tid : ThreadId}
        ------------------------------------------------
      → UniquePred ((EvInit ∪₁ HasTid tid) ∩₁ events ex)
    unique-po-pred wf =
      ∩₁-unique-pred
        (∪₁-unique-pred disjoint-init/tid init-unique has-tid-unique)
        (events-unique wf)


  unsplit-po-triʳ :
      {ex : Execution Label}
    → WellFormed ex
    → {x y z : Event Label}
    → po ex x z → po ex y z
      -----------------------------------
    → Tri (po ex x y) (x ≡ y) (po ex y x)
  unsplit-po-triʳ wf {x} {y} {z} po[xz] po[yz]
    with po-shared-tid₂' wf po[xz] po[yz]
  ... | tid , x-init/tid , y-init/tid , z-init/tid
    with po-tri wf tid (with-pred x (x-init/tid , poˡ∈ex wf po[xz])) (with-pred y (y-init/tid , poˡ∈ex wf po[yz]))
  ... | tri<  po[xy] x≢y ¬po[yx] = tri<  po[xy] (with-pred-≢ (unique-po-pred wf) x≢y) ¬po[yx]
  ... | tri≈ ¬po[xy] x≡y ¬po[yx] = tri≈ ¬po[xy] (with-pred-≡ x≡y) ¬po[yx]
  ... | tri> ¬po[xy] x≢y  po[yx] = tri> ¬po[xy] (with-pred-≢ (unique-po-pred wf) x≢y)  po[yx]


  w-rmw-dec : DecPred (EvWₜ trmw)
  w-rmw-dec (event-init _ _ _) = no (λ{(ev-init ())})
  w-rmw-dec (event-skip _ _)   = no (λ())
  w-rmw-dec (event _ _ lab) with labs-xopt lab
  w-rmw-dec (event _ _ lab) | xopt₁  a ¬b ¬c = no λ{(ev-w lab-w _) → ¬b lab-w}
  w-rmw-dec (event _ _ lab) | xopt₂ ¬a  b ¬c with inspect (lab-w-tag b)
  w-rmw-dec (event _ _ lab) | xopt₂ ¬a  b ¬c | tmov with≡ x = no (λ{(ev-w lab-w y) → 
    case labs-w-unique _ b lab-w of λ{refl → case (≡-trans y x) of λ()}})
  w-rmw-dec (event _ _ lab) | xopt₂ ¬a  b ¬c | trmw with≡ x = yes (ev-w b (≡-sym x))
  w-rmw-dec (event _ _ lab) | xopt₃ ¬a ¬b  c = no λ{(ev-w lab-w _) → ¬b lab-w}


  po-immˡ :
      {ex : Execution Label}
    → WellFormed ex
    → {x y z : Event Label}
    → po-imm ex x z → po-imm ex y z
      -----------------------------
    → x ≡ y
  po-immˡ wf {x} {y} {z} pi[xz] pi[yz] with unsplit-poʳ wf (proj₁ pi[xz]) pi[yz]
  ... | inj₁ refl = refl
  ... | inj₂ po[xy] = ⊥-elim (proj₂ pi[xz] (y , po[xy] , [ proj₁ pi[yz] ]))


  po-immʳ :
      {ex : Execution Label}
    → WellFormed ex
    → {x y z : Event Label}
    → ¬ EvInit x
    → po-imm ex x y → po-imm ex x z
      -----------------------------
    → y ≡ z
  po-immʳ wf {x} {y} {z} x-¬init pi[xy] pi[xz] with unsplit-poˡ wf x-¬init (proj₁ pi[xz]) pi[xy]
  ... | inj₁ y≡z    = y≡z
  ... | inj₂ po[yz] = ⊥-elim (proj₂ pi[xz] (y , proj₁ pi[xy] , [ po[yz] ]))


  rmw-dec :
      {ex : Execution Label}
    → WellFormed ex
      ------------------------
    → DecRel (rmw ex)
  rmw-dec wf x y with po-dec wf x y
  rmw-dec wf x y | no ¬po[xy] = no (λ{rmw[xy] → ¬po[xy] (proj₁ (⊆₂-apply (rmw-def wf) rmw[xy]))})
  rmw-dec wf x y | yes po[xy] with w-rmw-dec y
  rmw-dec {ex = ex} wf x y | yes po[xy] | yes y-w  =
    let (z , rmw[zy]) = ⇔₁-apply-⊇₁ (rmw-w wf) (poʳ∈ex wf po[xy] , y-w)
        pi[zy] = ⊆₂-apply (rmw-def wf) rmw[zy]
    in 
    case unsplit-poʳ wf po[xy] pi[zy] of
    λ{ (inj₁ x≡z) → yes (subst (λ τ → rmw ex τ y) (≡-sym x≡z) rmw[zy])
     ; (inj₂ po[xz]) → no (λ{rmw[xy] → proj₂ (⊆₂-apply (rmw-def wf) rmw[xy]) (z , po[xz] , [ proj₁ pi[zy] ])})
     }
  rmw-dec wf x y | yes po[xy] | no y-¬w = no (y-¬w ∘ ×₂-applyʳ (rmw-r×w wf))


  pi-dec :
      {ex : Execution Label}
    → WellFormed ex
      ---------------------------
    → DecRel (po-imm ex)
  pi-dec wf x y with po-dec wf x y
  pi-dec wf x y | yes po[xy] with ⇔₂-apply-⊆₂ (po-splittable wf) po[xy]
  pi-dec wf x y | yes po[xy] | [ pi[xy] ] = yes pi[xy]
  pi-dec wf x y | yes po[xy] | _∷_ {x} {z} pi[xz] pi⁺[zy] =
    no (λ{pi[xy] → proj₂ pi[xy] (z , proj₁ pi[xz] , ⁺-map _ proj₁ pi⁺[zy])})
  pi-dec wf x y | no ¬po[xy] = no (λ{pi[xy] → ¬po[xy] (proj₁ pi[xy])})

  po⁺⇒po :
      {ex : Execution Label}
    → WellFormed ex
    → {x y : Event Label}
    → TransClosure (po ex) x y
    → po ex x y
  po⁺⇒po = ⁺-join-trans ∘ po-trans
