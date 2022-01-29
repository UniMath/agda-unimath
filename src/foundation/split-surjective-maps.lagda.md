# Split surjective maps

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.split-surjective-maps where

open import foundation.dependent-pair-types using (Σ)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A map `f : A → B` is split surjective if we can construct for every `b : B` an element `a : A` equipped with an identification `Id (f a) b`.

## Warning

Note that split-surjectiveness is the Curry-Howard interpretation of surjectiveness. However, this is not a property, and the split surjective maps don't fit in a factorization system along with the injective maps. 

## Definition

```agda
is-split-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-split-surjective {A = A} {B} f = (b : B) → Σ A (λ a → Id (f a) b)
```
