------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for types of dependent functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from
-- `Function.Dependent`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous
  hiding (IsEquivalence; Rel; Setoid)
open import Data.Product using (∃; _×_; _,_)
open import Level using (_⊔_)

module Function.Dependent.Structures
  {a b ℓ₁ ℓ₂}
  {A : Set a}        -- Domain
  (B : A → Set b)    -- Dependent codomain
  (_≈₁_ : Rel A ℓ₁)  -- Equality over the domain
  (_≈₂_ : IRel B ℓ₂) -- Dependent equality over the codomains
  where

open import Function.Dependent.Definitions B _≈₁_ _≈₂_

------------------------------------------------------------------------
-- One element structures
------------------------------------------------------------------------

record IsDependentFunc (f : (a : A) → B a) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    cong           : Congruent f
    isEquivalence₁ : IsEquivalence _≈₁_
    isEquivalence₂ : IsIndexedEquivalence B _≈₂_

  module Eq₁ where

    setoid : Setoid a ℓ₁
    setoid = record
      { isEquivalence = isEquivalence₁
      }

    open Setoid setoid public

  module Eq₂ where

    indexedSetoid : IndexedSetoid A b ℓ₂
    indexedSetoid = record
      { isEquivalence = isEquivalence₂
      }

    open IndexedSetoid indexedSetoid public


record IsDependentInjection (f : (a : A) → B a) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsDependentFunc f
    injective   : Injective f

  open IsDependentFunc isCongruent public


record IsDependentSurjection (f : (a : A) → B a) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isCongruent : IsDependentFunc f
    surjective  : Surjective f

  open IsDependentFunc isCongruent public


record IsDependentBijection (f : (a : A) → B a) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isInjection : IsDependentInjection f
    surjective  : Surjective f

  open IsDependentInjection isInjection public

  bijective : Bijective f
  bijective = injective , surjective

  isSurjection : IsDependentSurjection f
  isSurjection = record
    { isCongruent = isCongruent
    ; surjective  = surjective
    }
