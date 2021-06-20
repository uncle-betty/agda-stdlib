------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for types of dependent functions
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from
-- `Function.Dependent`.

-- Note that these bundles differ from those found elsewhere in other
-- library hierarchies as they take Setoids as parameters. This is
-- because a function is of no use without knowing what its domain and
-- codomain is, as well which equalities are being considered over them.
-- One consequence of this is that they are not built from the
-- definitions found in `Function.Dependent.Structures` as is usually
-- the case in other hierarchies in the library, as this would duplicate
-- the equality axioms.

{-# OPTIONS --without-K --safe #-}

module Function.Dependent.Bundles where

import Function.Dependent.Definitions as FunctionDefinitions
import Function.Dependent.Structures as FunctionStructures

open import Level using (Level; _⊔_; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)
open import Relation.Binary.Indexed.Heterogeneous using (IndexedSetoid)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial as Trivial

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Setoid bundles
------------------------------------------------------------------------

module _ (From : Setoid a ℓ₁)
         (To : IndexedSetoid (Setoid.Carrier From) b ℓ₂)
         where

  open Setoid From      using () renaming (Carrier to A; _≈_ to _≈₁_)
  open IndexedSetoid To using () renaming (Carrier to B; _≈_ to _≈₂_)
  open FunctionDefinitions B _≈₁_ _≈₂_
  open FunctionStructures  B _≈₁_ _≈₂_

------------------------------------------------------------------------
-- Bundles with one element

  -- Called `Func` rather than `Function` in order to avoid clashing
  -- with the top-level module.
  record DependentFunc : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f    : (a : A) → B a
      cong : Congruent f

    isDependentFunc : IsDependentFunc f
    isDependentFunc = record
      { cong           = cong
      ; isEquivalence₁ = Setoid.isEquivalence From
      ; isEquivalence₂ = IndexedSetoid.isEquivalence To
      }

    open IsDependentFunc isDependentFunc public
      using (module Eq₁; module Eq₂)


  record DependentInjection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f           : (a : A) → B a
      cong        : Congruent f
      injective   : Injective f

    function : DependentFunc
    function = record
      { f    = f
      ; cong = cong
      }

    open DependentFunc function public
      hiding (f; cong)

    isInjection : IsDependentInjection f
    isInjection = record
      { isCongruent = isDependentFunc
      ; injective   = injective
      }


  record DependentSurjection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f          : (a : A) → B a
      cong       : Congruent f
      surjective : Surjective f

    isDependentFunc : IsDependentFunc f
    isDependentFunc = record
      { cong           = cong
      ; isEquivalence₁ = Setoid.isEquivalence From
      ; isEquivalence₂ = IndexedSetoid.isEquivalence To
      }

    open IsDependentFunc isDependentFunc public
      using (module Eq₁; module Eq₂)

    isSurjection : IsDependentSurjection f
    isSurjection = record
      { isCongruent = isDependentFunc
      ; surjective  = surjective
      }


  record DependentBijection : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      f         : (a : A) → B a
      cong      : Congruent f
      bijective : Bijective f

    injective : Injective f
    injective = proj₁ bijective

    surjective : Surjective f
    surjective = proj₂ bijective

    dependentInjection : DependentInjection
    dependentInjection = record
      { cong      = cong
      ; injective = injective
      }

    dependentSurjection : DependentSurjection
    dependentSurjection = record
      { cong       = cong
      ; surjective = surjective
      }

    open DependentInjection  dependentInjection  public using (isInjection)
    open DependentSurjection dependentSurjection public using (isSurjection)

    isBijection : IsDependentBijection f
    isBijection = record
      { isInjection = isInjection
      ; surjective  = surjective
      }

    open IsDependentBijection isBijection public
      using (module Eq₁; module Eq₂)


------------------------------------------------------------------------
-- Bundles specialised for propositional equality
------------------------------------------------------------------------

infix 3 _⟶_ _↣_ _↠_ _⤖_
_⟶_ : (A : Set a) → (A → Set b) → Set _
A ⟶ B = DependentFunc (≡.setoid A) (record { Carrier = B ; _≈_ = {!_≡_!} ; isEquivalence = {!!} }) --(Trivial.indexedSetoid (≡.setoid B))

_↣_ : (A : Set a) → (A → Set b) → Set _
A ↣ B = DependentInjection (≡.setoid A) {!!} --(Trivial.indexedSetoid (≡.setoid B))

_↠_ : (A : Set a) → (A → Set b) → Set _
A ↠ B = DependentSurjection (≡.setoid A) {!!} --(Trivial.indexedSetoid (≡.setoid B))

_⤖_ : (A : Set a) → (A → Set b) → Set _
A ⤖ B = DependentBijection (≡.setoid A) {!!} --(Trivial.indexedSetoid (≡.setoid B))

-- We now define some constructors for the above that
-- automatically provide the required congruency proofs.

module _ {A : Set a} {B : A → Set b} where

  open FunctionDefinitions {A = A} B _≡_ {!!}

  mk⟶ : ((a : A) → B a) → A ⟶ {!!}
  mk⟶ f = record
    { f         = {!!} --f
    ; cong      = {!!} --≡.cong f
    }
{-
  mk↣ : ∀ {f : A → B} → Injective f → A ↣ B
  mk↣ {f} inj = record
    { f         = f
    ; cong      = ≡.cong f
    ; injective = inj
    }

  mk↠ : ∀ {f : A → B} → Surjective f → A ↠ B
  mk↠ {f} surj = record
    { f          = f
    ; cong       = ≡.cong f
    ; surjective = surj
    }

  mk⤖ : ∀ {f : A → B} → Bijective f → A ⤖ B
  mk⤖ {f} bij = record
    { f         = f
    ; cong      = ≡.cong f
    ; bijective = bij
    }
-}
