# Double counting

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-combinatorics.double-counting where

open import elementary-number-theory.equivalences-standard-finite-types using
  ( is-injective-Fin)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; inv-equiv; _∘e_; id-equiv)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; number-of-elements-count)
```

## Idea

Given two countings of the same type, we obtain the same number of its elements. Likewise, given two countings of equivalent types, we obtain the same number of their elements.

```agda
abstract
  double-counting-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) (e : A ≃ B) →
    Id (number-of-elements-count count-A) (number-of-elements-count count-B)
  double-counting-equiv (pair k f) (pair l g) e =
    is-injective-Fin ((inv-equiv g ∘e e) ∘e f)

abstract
  double-counting :
    {l : Level} {A : UU l} (count-A count-A' : count A) →
    Id (number-of-elements-count count-A) (number-of-elements-count count-A')
  double-counting count-A count-A' =
    double-counting-equiv count-A count-A' id-equiv
```
