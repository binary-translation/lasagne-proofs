{-# OPTIONS --without-K --safe #-}


-- | A typical utilities file. It contains some general lemmas that were
-- missing in the standard library.
module Helpers where

-- Stdlib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong) renaming (sym to ≡-sym; trans to ≡-trans)
open import Level using (Level; _⊔_)
open import Function using (_∘_; _∘₂_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using (REL; IsEquivalence; Trans; Symmetric)


-- # General Helpers


contrapositive : {a b : Level} {A : Set a} {B : Set b}
  → ( A → B )
    -------------
  → ( ¬ B → ¬ A )
contrapositive f ¬b a = ¬b (f a)


-- | Helper. The value given for `¬ A` is often `λ ()`. However, the type of `λ ()`
-- is often ambiguous. Here, its type can be inferred from the inhabitant of `A`.
contradict : {a : Level} {A : Set a}
  → A
  → ¬ A
    ---
  → ⊥
contradict a ¬a = ¬a a


-- | Helper. The value given for `¬ A` is often `λ ()`. However, the type of `λ ()`
-- is often ambiguous. Here, its type can be inferred from the inhabitant of `A`.
absurd : {a b : Level} {A : Set a} {B : Set b}
  → A
  → ¬ A
    ---
  → B
absurd = ⊥-elim ∘₂ contradict



-- # Binary Relations


-- | Two-step transitivity.
--
-- Intuitively: `(P ⨾ Q ⨾ R) x y → S x y`
Trans₂ : {a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  → REL A B ℓ₁ → REL B C ℓ₂ → REL C D ℓ₃ → REL A D ℓ₄ → Set _
Trans₂ P Q R S = ∀ {i j k l} → P i j → Q j k → R k l → S i l



-- # Sum (_⊎_)


⊎-elim : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
  → ( A → C )
  → ( B → C )
    ---------
  → A ⊎ B → C
⊎-elim f _ (inj₁ a) = f a
⊎-elim _ g (inj₂ b) = g b


⊥⊎-elim : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
  → ( A → ⊥ )
  → ( B → C )
    ---------
  → A ⊎ B → C
⊥⊎-elim f = ⊎-elim (⊥-elim ∘ f)


⊎⊥-elim : {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
  → ( A → C )
  → ( B → ⊥ )
    ---------
  → A ⊎ B → C
⊎⊥-elim f g = ⊎-elim f (⊥-elim ∘ g)


¬sum : {a b : Level} {A : Set a} {B : Set b}
  → ¬ A
  → ¬ B
    ---------
  → ¬ (A ⊎ B)
¬sum ¬x ¬y (inj₁ x) = ¬x x
¬sum ¬x ¬y (inj₂ y) = ¬y y


sumʳ : {a b : Level} {A : Set a} {B : Set b}
  → ¬ A
  → A ⊎ B
    -----
  → B
sumʳ ¬x (inj₁ x) = ⊥-elim (¬x x)
sumʳ ¬y (inj₂ y) = y


sumˡ : {a b : Level} {A : Set a} {B : Set b}
  → ¬ B
  → A ⊎ B
    -----
  → A
sumˡ ¬y (inj₁ x) = x
sumˡ ¬y (inj₂ y) = ⊥-elim (¬y y)



-- # Equality


≢-sym : {a : Level} {A : Set a} → {x y : A}
  → x ≢ y
    -----
  → y ≢ x
≢-sym x≢y refl = x≢y refl


≡-equivalence : ∀ {a : Level} {A : Set a}
  → IsEquivalence {a} {_} {A} _≡_
≡-equivalence =
  record
    { refl   =  refl
    ; sym    =  ≡-sym
    ; trans  =  ≡-trans
    }


cong₃ : ∀ {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  → (f : A → B → C → D)
  → {x p : A}
  → x ≡ p
  → {y q : B}
  → y ≡ q
  → {z r : C}
  → z ≡ r
    -----------------
  → f x y z ≡ f p q r
cong₃ f refl refl refl = refl


cong₄ : ∀ {a b c d e f : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → (f : A → B → C → D → E)
  → {v p : A}
  → v ≡ p
  → {w q : B}
  → w ≡ q
  → {x r : C}
  → x ≡ r
  → {y s : D}
  → y ≡ s
    ---------------------
  → f v w x y ≡ f p q r s
cong₄ f refl refl refl refl = refl


cong₅ : ∀ {a b c d e f : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} {F : Set f}
  → (f : A → B → C → D → E → F)
  → {v p : A}
  → v ≡ p
  → {w q : B}
  → w ≡ q
  → {x r : C}
  → x ≡ r
  → {y s : D}
  → y ≡ s
  → {z t : E}
  → z ≡ t
    -------------------------
  → f v w x y z ≡ f p q r s t
cong₅ f refl refl refl refl refl = refl


cong-dec : ∀ {a b : Level} {A : Set a} {B : Set b}
  → (f : A → B)
  → (∀ {x y : A} → f x ≡ f y → x ≡ y)
  → {x y : A}
  → Dec (x ≡ y)
    ---------------
  → Dec (f x ≡ f y)
cong-dec f f₁ (yes refl) = yes refl
cong-dec f f₁ (no x≢y)   = no (x≢y ∘ f₁)


cong₂-dec : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c}
  → (f : A → B → C)
  → (∀ {x y : A} {w z : B} → f x w ≡ f y z → x ≡ y)
  → (∀ {x y : A} {w z : B} → f x w ≡ f y z → w ≡ z)
  → {x y : A}
  → {w z : B}
  → Dec (x ≡ y)
  → Dec (w ≡ z)
    -------------------
  → Dec (f x w ≡ f y z)
cong₂-dec f f₁ f₂ (yes refl) (yes refl) = yes refl
cong₂-dec f f₁ f₂ (yes refl) (no w≢z)   = no (w≢z ∘ f₂)
cong₂-dec f f₁ f₂ (no x≢y)   _          = no (x≢y ∘ f₁)


cong₃-dec : ∀ {a b c d : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  → (f : A → B → C → D)
  → (∀ {x y : A} {w z : B} {p q : C} → f x w p ≡ f y z q → x ≡ y)
  → (∀ {x y : A} {w z : B} {p q : C} → f x w p ≡ f y z q → w ≡ z)
  → (∀ {x y : A} {w z : B} {p q : C} → f x w p ≡ f y z q → p ≡ q)
  → {x y : A}
  → {w z : B}
  → {p q : C}
  → Dec (x ≡ y)
  → Dec (w ≡ z)
  → Dec (p ≡ q)
    -----------------------
  → Dec (f x w p ≡ f y z q)
cong₃-dec f f₁ f₂ f₃ (yes refl) (yes refl) (yes refl) = yes refl
cong₃-dec f f₁ f₂ f₃ (yes refl) (yes refl) (no p≢q)   = no (p≢q ∘ f₃)
cong₃-dec f f₁ f₂ f₃ (yes refl) (no w≢z)   _          = no (w≢z ∘ f₂)
cong₃-dec f f₁ f₂ f₃ (no x≢y)   _          _          = no (x≢y ∘ f₁)



-- # Decidable


ℕ-dec : ∀ (x y : ℕ) → Dec (x ≡ y)
ℕ-dec zero    zero    = yes refl
ℕ-dec (suc x) (suc y) = cong-suc (ℕ-dec x y)
  where
  cong-suc : ∀ {x y : ℕ} → Dec (x ≡ y) → Dec (suc x ≡ suc y)
  cong-suc (yes x≡y) = yes (cong suc x≡y)
  cong-suc (no  x≢y) = no λ{refl → x≢y refl}
ℕ-dec zero    (suc _) = no (λ ())
ℕ-dec (suc _) zero    = no (λ ())


×-dec : {a b : Level} {A : Set a} {B : Set b}
  → Dec A
  → Dec B
    -----------
  → Dec (A × B)
×-dec (yes a) (yes b) = yes (a , b)
×-dec (yes a) (no ¬b) = no (¬b ∘ proj₂)
×-dec (no ¬a) _       = no (¬a ∘ proj₁)


-- # Type-checking helpers


data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x


-- | When matching on a variable, we may need to remember it is equal.
inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl


-- | Pattern-matching on a constructor is often clumsy. This function makes it
-- more convenient.
--
-- # Example
--
-- ```
-- case x of
-- λ{ inj₁ x → ?
--  ; inj₂ y → ?
--  }
-- ```
case_of_ : ∀ {a b} {A : Set a} {B : Set b}
  → A
  → (A → B)
    -------
  → B
case x of f = f x


-- | Allows pattern-matching simultaneously on two values.
--
-- See also `case_of_`.
case₂_and_of_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  → A
  → B
  → (A → B → C)
    -----------
  → C
case₂ x and y of f = f x y



-- # Exclusive option


-- | Exclusive option. Exactly one can be true at a time.
--
-- (This is in contrast to non-exclusive options like `a ⊎ b`, where both could be true)
data XOpt₅ {a b c d e : Level} (A : Set a) (B : Set b) (C : Set c) (D : Set d) (E : Set e) : Set (a ⊔ b ⊔ c ⊔ d ⊔ e) where
  xopt₁ : ( a :   A) → (¬b : ¬ B) → (¬c : ¬ C) → (¬d : ¬ D) → (¬e : ¬ E) → XOpt₅ A B C D E
  xopt₂ : (¬a : ¬ A) → ( b :   B) → (¬c : ¬ C) → (¬d : ¬ D) → (¬e : ¬ E) → XOpt₅ A B C D E
  xopt₃ : (¬a : ¬ A) → (¬b : ¬ B) → ( c :   C) → (¬d : ¬ D) → (¬e : ¬ E) → XOpt₅ A B C D E
  xopt₄ : (¬a : ¬ A) → (¬b : ¬ B) → (¬c : ¬ C) → ( d :   D) → (¬e : ¬ E) → XOpt₅ A B C D E
  xopt₅ : (¬a : ¬ A) → (¬b : ¬ B) → (¬c : ¬ C) → (¬d : ¬ D) → ( e :   E) → XOpt₅ A B C D E


private
  -- Helpers: Generalizations over `xm` and `select`
  
  xopt₅-h₁ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
    → XOpt₅ A B C D E
      ---------------------------------
    → (A × ¬ B × ¬ C × ¬ D × ¬ E) ⊎ ¬ A
  xopt₅-h₁ (xopt₁  a ¬b ¬c ¬d ¬e) = inj₁ (a , ¬b , ¬c , ¬d , ¬e)
  xopt₅-h₁ (xopt₂ ¬a  _  _  _  _) = inj₂ ¬a
  xopt₅-h₁ (xopt₃ ¬a  _  _  _  _) = inj₂ ¬a
  xopt₅-h₁ (xopt₄ ¬a  _  _  _  _) = inj₂ ¬a
  xopt₅-h₁ (xopt₅ ¬a  _  _  _  _) = inj₂ ¬a


  xopt₅-h₂ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
    → XOpt₅ A B C D E
      ---------------------------------
    → (B × ¬ A × ¬ C × ¬ D × ¬ E) ⊎ ¬ B
  xopt₅-h₂ (xopt₁  _ ¬b  _  _  _) = inj₂ ¬b
  xopt₅-h₂ (xopt₂ ¬a  b ¬c ¬d ¬e) = inj₁ (b , ¬a , ¬c , ¬d , ¬e)
  xopt₅-h₂ (xopt₃  _ ¬b  _  _  _) = inj₂ ¬b
  xopt₅-h₂ (xopt₄  _ ¬b  _  _  _) = inj₂ ¬b
  xopt₅-h₂ (xopt₅  _ ¬b  _  _  _) = inj₂ ¬b


  xopt₅-h₃ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
    → XOpt₅ A B C D E
      ---------------------------------
    → (C × ¬ A × ¬ B × ¬ D × ¬ E) ⊎ ¬ C
  xopt₅-h₃ (xopt₁  _  _ ¬c  _  _) = inj₂ ¬c
  xopt₅-h₃ (xopt₂  _  _ ¬c  _  _) = inj₂ ¬c
  xopt₅-h₃ (xopt₃ ¬a ¬b  c ¬d ¬e) = inj₁ (c , ¬a , ¬b , ¬d , ¬e)
  xopt₅-h₃ (xopt₄  _  _ ¬c  _  _) = inj₂ ¬c
  xopt₅-h₃ (xopt₅  _  _ ¬c  _  _) = inj₂ ¬c


  xopt₅-h₄ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
    → XOpt₅ A B C D E
      ---------------------------------
    → (D × ¬ A × ¬ B × ¬ C × ¬ E) ⊎ ¬ D
  xopt₅-h₄ (xopt₁  _  _  _ ¬d  _) = inj₂ ¬d
  xopt₅-h₄ (xopt₂  _  _  _ ¬d  _) = inj₂ ¬d
  xopt₅-h₄ (xopt₃  _  _  _ ¬d  _) = inj₂ ¬d
  xopt₅-h₄ (xopt₄ ¬a ¬b ¬c  d ¬e) = inj₁ (d , ¬a , ¬b , ¬c , ¬e)
  xopt₅-h₄ (xopt₅  _  _  _ ¬d  _) = inj₂ ¬d


  xopt₅-h₅ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
    → XOpt₅ A B C D E
      ---------------------------------
    → (E × ¬ A × ¬ B × ¬ C × ¬ D) ⊎ ¬ E
  xopt₅-h₅ (xopt₁  _  _  _  _ ¬e) = inj₂ ¬e
  xopt₅-h₅ (xopt₂  _  _  _  _ ¬e) = inj₂ ¬e
  xopt₅-h₅ (xopt₃  _  _  _  _ ¬e) = inj₂ ¬e
  xopt₅-h₅ (xopt₄  _  _  _  _ ¬e) = inj₂ ¬e
  xopt₅-h₅ (xopt₅ ¬a ¬b ¬c ¬d  e) = inj₁ (e , ¬a , ¬b , ¬c , ¬d)


xopt₅-xm₁ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → XOpt₅ A B C D E
    ---------------
  → A ⊎ ¬ A
xopt₅-xm₁ = Sum.map₁ proj₁ ∘ xopt₅-h₁


xopt₅-xm₂ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → XOpt₅ A B C D E
    ---------------
  → B ⊎ ¬ B
xopt₅-xm₂ = Sum.map₁ proj₁ ∘ xopt₅-h₂


xopt₅-xm₃ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → XOpt₅ A B C D E
    ---------------
  → C ⊎ ¬ C
xopt₅-xm₃ = Sum.map₁ proj₁ ∘ xopt₅-h₃


xopt₅-xm₄ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → XOpt₅ A B C D E
    ---------------
  → D ⊎ ¬ D
xopt₅-xm₄ = Sum.map₁ proj₁ ∘ xopt₅-h₄


xopt₅-xm₅ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → XOpt₅ A B C D E
    ---------------
  → E ⊎ ¬ E
xopt₅-xm₅ = Sum.map₁ proj₁ ∘ xopt₅-h₅


xopt₅-select₁ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → A
  → XOpt₅ A B C D E
    ---------------------
  → ¬ B × ¬ C × ¬ D × ¬ E
xopt₅-select₁ a x with xopt₅-h₁ x
... | inj₁ a× = proj₂ a×
... | inj₂ ¬a = ⊥-elim (¬a a)


xopt₅-select₂ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → B
  → XOpt₅ A B C D E
    ---------------------
  → ¬ A × ¬ C × ¬ D × ¬ E
xopt₅-select₂ b x with xopt₅-h₂ x
... | inj₁ b× = proj₂ b×
... | inj₂ ¬b = ⊥-elim (¬b b)


xopt₅-select₃ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → C
  → XOpt₅ A B C D E
    ---------------------
  → ¬ A × ¬ B × ¬ D × ¬ E
xopt₅-select₃ c x with xopt₅-h₃ x
... | inj₁ c× = proj₂ c×
... | inj₂ ¬c = ⊥-elim (¬c c)


xopt₅-select₄ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → D
  → XOpt₅ A B C D E
    ---------------------
  → ¬ A × ¬ B × ¬ C × ¬ E
xopt₅-select₄ d x with xopt₅-h₄ x
... | inj₁ d× = proj₂ d×
... | inj₂ ¬d = ⊥-elim (¬d d)


xopt₅-select₅ : {a b c d e : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → E
  → XOpt₅ A B C D E
    ---------------------
  → ¬ A × ¬ B × ¬ C × ¬ D
xopt₅-select₅ e x with xopt₅-h₅ x
... | inj₁ e× = proj₂ e×
... | inj₂ ¬e = ⊥-elim (¬e e)


-- | Non-exclusive ternary option.
--
-- This is an alternative to `a ⊎ b ⊎ c`, where pattern-matching is clumsy.
data Opt₃ {ℓ : Level} (A B C : Set ℓ) : Set ℓ where
  opt₁ : A → Opt₃ A B C
  opt₂ : B → Opt₃ A B C
  opt₃ : C → Opt₃ A B C


-- | Ternary alternative for `_∪₁_`.
OptPred₃ : {a ℓ : Level} {A : Set a}
  → Pred A ℓ → Pred A ℓ → Pred A ℓ
    ------------------------------
  → Pred A ℓ
OptPred₃ P₁ P₂ P₃ x = Opt₃ (P₁ x) (P₂ x) (P₃ x)
