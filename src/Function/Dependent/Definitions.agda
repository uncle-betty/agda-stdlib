------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from
-- `Function.Dependent`.

{-# OPTIONS --without-K --safe #-}

open import Data.Product using (∃; _×_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous using (IRel)

module Function.Dependent.Definitions
  {a b ℓ₁ ℓ₂}
  {A : Set a}        -- Domain
  (B : A → Set b)    -- Dependent codomain
  (_≈₁_ : Rel A ℓ₁)  -- Equality over the domain
  (_≈₂_ : IRel B ℓ₂) -- Dependent equality over the codomain
  where

------------------------------------------------------------------------
-- Definitions

Congruent : ((a : A) → B a) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

Injective : ((a : A) → B a) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

Surjective : ((a : A) → B a) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Surjective f = ∀ {a} (y : B a) → ∃ λ x → ∀ z → z ≈₁ x → f z ≈₂ y

Bijective : ((a : A) → B a) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Bijective f = Injective f × Surjective f
