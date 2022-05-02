---
title: The groupoid of main classes of Latin hypercubes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.main-classes-of-latin-hypercubes where

open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.products-unordered-tuples-of-types
open import foundation.universe-levels
open import foundation.unordered-tuples
open import foundation.unordered-tuples-of-types
```

## Definition

```agda
Main-Class-Latin-Hypercube : (l1 l2 : Level) (n : ℕ) → UU (lsuc l1 ⊔ lsuc l2)
Main-Class-Latin-Hypercube l1 l2 n =
  Σ ( unordered-tuple-types l1 (succ-ℕ n))
    ( λ A →
      Σ ( product-unordered-tuple-types A → UU l2)
        ( λ R →
          ( i : type-unordered-tuple A)
          ( f : product-unordered-tuple-types
                (unordered-tuple-complement-point-type-unordered-tuple A i)) →
          is-contr
            ( Σ ( element-unordered-tuple A i)
                ( λ a →
                  R (map-equiv-pr-product-unordered-tuple-types A i f a)))))
```
