------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warning=noUserWarning #-}

module Function.Inverse where

{-# WARNING_ON_IMPORT
"Function.Inverse was deprecated in v2.0.
Use the standard function hierarchy in Function/Function.Bundles instead."
#-}

open import Level
open import Function.Base using (flip)
open import Function.Bijection hiding (id; _∘_; bijection)
open import Function.Equality as F
  using (_⟶_) renaming (_∘_ to _⟪∘⟫_)
open import Function.LeftInverse as Left hiding (id; _∘_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; TransFlip; Sym)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_; _≡_)
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Inverses

record _InverseOf_ {f₁ f₂ t₁ t₂}
                   {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
                   (from : To ⟶ From) (to : From ⟶ To) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    left-inverse-of  : from LeftInverseOf  to
    right-inverse-of : from RightInverseOf to
{-# WARNING_ON_USAGE _InverseOf_
"Warning: _InverseOf_ was deprecated in v2.0.
Please use Function.(Structures.)IsInverse instead."
#-}

------------------------------------------------------------------------
-- The set of all inverses between two setoids

record Inverse {f₁ f₂ t₁ t₂}
               (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
               Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to         : From ⟶ To
    from       : To ⟶ From
    inverse-of : from InverseOf to

  open _InverseOf_ inverse-of public

  left-inverse : LeftInverse From To
  left-inverse = record
    { to              = to
    ; from            = from
    ; left-inverse-of = left-inverse-of
    }

  open LeftInverse left-inverse public
    using (injective; injection)

  bijection : Bijection From To
  bijection = record
    { to        = to
    ; bijective = record
      { injective  = injective
      ; surjective = record
        { from             = from
        ; right-inverse-of = right-inverse-of
        }
      }
    }

  open Bijection bijection public
    using (equivalence; surjective; surjection; right-inverse;
           to-from; from-to)
{-# WARNING_ON_USAGE Inverse
"Warning: Inverse was deprecated in v2.0.
Please use Function.(Bundles.)Inverse instead."
#-}

------------------------------------------------------------------------
-- The set of all inverses between two sets (i.e. inverses with
-- propositional equality)

infix 3 _↔_ _↔̇_

_↔_ : ∀ {f t} → Set f → Set t → Set _
From ↔ To = Inverse (≡.setoid From) (≡.setoid To)
{-# WARNING_ON_USAGE _↔_
"Warning: _↔_ was deprecated in v2.0.
Please use Function.(Bundles.)_↔_ instead."
#-}

_↔̇_ : ∀ {i f t} {I : Set i} → Pred I f → Pred I t → Set _
From ↔̇ To = ∀ {i} → From i ↔ To i
{-# WARNING_ON_USAGE _↔̇_
"Warning: _↔̇_ was deprecated in v2.0.
Please use Function.Indexed.(Bundles.)_↔ᵢ_ instead."
#-}

inverse : ∀ {f t} {From : Set f} {To : Set t} →
          (to : From → To) (from : To → From) →
          (∀ x → from (to x) ≡ x) →
          (∀ x → to (from x) ≡ x) →
          From ↔ To
inverse to from from∘to to∘from = record
  { to   = F.→-to-⟶ to
  ; from = F.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
{-# WARNING_ON_USAGE inverse
"Warning: inverse was deprecated in v2.0.
Please use Function.(Bundles.)mk↔ instead."
#-}

------------------------------------------------------------------------
-- If two setoids are in bijective correspondence, then there is an
-- inverse between them

fromBijection :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  Bijection From To → Inverse From To
fromBijection b = record
  { to         = Bijection.to b
  ; from       = Bijection.from b
  ; inverse-of = record
    { left-inverse-of  = Bijection.left-inverse-of b
    ; right-inverse-of = Bijection.right-inverse-of b
    }
  }

------------------------------------------------------------------------
-- Inverse is an equivalence relation

-- Reflexivity

id : ∀ {s₁ s₂} → Reflexive (Inverse {s₁} {s₂})
id {x = S} = record
  { to         = F.id
  ; from       = F.id
  ; inverse-of = record
    { left-inverse-of  = LeftInverse.left-inverse-of id′
    ; right-inverse-of = LeftInverse.left-inverse-of id′
    }
  } where id′ = Left.id {S = S}
{-# WARNING_ON_USAGE id
"Warning: id was deprecated in v2.0.
Please use either Function.Properties.Inverse.refl or
Function.Construct.Identity.inverse instead."
#-}

-- Transitivity

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂} →
      TransFlip (Inverse {f₁} {f₂} {m₁} {m₂})
                (Inverse {m₁} {m₂} {t₁} {t₂})
                (Inverse {f₁} {f₂} {t₁} {t₂})
f ∘ g = record
  { to         = to   f ⟪∘⟫ to   g
  ; from       = from g ⟪∘⟫ from f
  ; inverse-of = record
    { left-inverse-of  = LeftInverse.left-inverse-of (Left._∘_ (left-inverse  f) (left-inverse  g))
    ; right-inverse-of = LeftInverse.left-inverse-of (Left._∘_ (right-inverse g) (right-inverse f))
    }
  } where open Inverse
{-# WARNING_ON_USAGE _∘_
"Warning: _∘_ was deprecated in v2.0.
Please use either Function.Properties.Inverse.trans or
Function.Construct.Composition.inverse instead."
#-}

-- Symmetry.

sym : ∀ {f₁ f₂ t₁ t₂} →
      Sym (Inverse {f₁} {f₂} {t₁} {t₂}) (Inverse {t₁} {t₂} {f₁} {f₂})
sym inv = record
  { from       = to
  ; to         = from
  ; inverse-of = record
    { left-inverse-of  = right-inverse-of
    ; right-inverse-of = left-inverse-of
    }
  } where open Inverse inv
{-# WARNING_ON_USAGE sym
"Warning: sym was deprecated in v2.0.
Please use either Function.Properties.Inverse.sym or
Function.Construct.Symmetry.inverse instead."
#-}

------------------------------------------------------------------------
-- Transformations

map : ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
        {f₁′ f₂′ t₁′ t₂′}
        {From′ : Setoid f₁′ f₂′} {To′ : Setoid t₁′ t₂′} →
      (t : (From ⟶ To) → (From′ ⟶ To′)) →
      (f : (To ⟶ From) → (To′ ⟶ From′)) →
      (∀ {to from} → from InverseOf to → f from InverseOf t to) →
      Inverse From To → Inverse From′ To′
map t f pres eq = record
  { to         = t to
  ; from       = f from
  ; inverse-of = pres inverse-of
  } where open Inverse eq

zip : ∀ {f₁₁ f₂₁ t₁₁ t₂₁}
        {From₁ : Setoid f₁₁ f₂₁} {To₁ : Setoid t₁₁ t₂₁}
        {f₁₂ f₂₂ t₁₂ t₂₂}
        {From₂ : Setoid f₁₂ f₂₂} {To₂ : Setoid t₁₂ t₂₂}
        {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
      (t : (From₁ ⟶ To₁) → (From₂ ⟶ To₂) → (From ⟶ To)) →
      (f : (To₁ ⟶ From₁) → (To₂ ⟶ From₂) → (To ⟶ From)) →
      (∀ {to₁ from₁ to₂ from₂} →
         from₁ InverseOf to₁ → from₂ InverseOf to₂ →
         f from₁ from₂ InverseOf t to₁ to₂) →
      Inverse From₁ To₁ → Inverse From₂ To₂ → Inverse From To
zip t f pres eq₁ eq₂ = record
  { to         = t (to   eq₁) (to   eq₂)
  ; from       = f (from eq₁) (from eq₂)
  ; inverse-of = pres (inverse-of eq₁) (inverse-of eq₂)
  } where open Inverse
