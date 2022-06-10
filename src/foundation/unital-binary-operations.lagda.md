# Unital binary operations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.unital-binary-operations where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (UU; Level)
```

## Idea

A binary operation of type `A → A → A` is unital if there is a unit of type `A` that satisfies both the left and right unit laws.


```agda
is-unital : {l : Level} {A : UU l} (op : A → A → A) → UU l
is-unital {A = A} op =
  Σ A
    ( λ u →
      ( (x : A) → Id (op u x) x) ×
      ( (x : A) → Id (op x u) x))
```

Furthermore, an binary operation is _coherently_ unital if the proofs of left and right unit laws agree on the case where both arguments of the operation are the unit.

```agda
is-coherently-unital : {l : Level} {A : UU l} (op : A → A → A) → UU l
is-coherently-unital {A = A} op =
  Σ A
    ( λ u →
      Σ ( (x : A) → Id (op u x) x)
        ( λ α →
          Σ ( (x : A) → Id (op x u) x)
            ( λ β → Id (α u) (β u))))
```
