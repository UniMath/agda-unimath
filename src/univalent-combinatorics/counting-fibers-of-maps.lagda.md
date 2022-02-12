# Counting the elements in the fiber of a map

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-fibers-of-maps where

open import elementary-number-theory.sums-of-natural-numbers using
  ( sum-count-ℕ)

open import foundation.fibers-of-maps using (fib; equiv-total-fib)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; count-equiv'; number-of-elements-count)
open import univalent-combinatorics.counting-dependent-pair-types using
  ( count-fiber-count-Σ; sum-number-of-elements-count-fiber-count-Σ)
open import univalent-combinatorics.double-counting using (double-counting)
```

### If A and B can be counted, then the fibers of a map f : A → B can be counted

```agda
count-fib :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  count A → count B → (y : B) → count (fib f y)
count-fib f count-A count-B =
  count-fiber-count-Σ count-B (count-equiv' (equiv-total-fib f) count-A)
```

```agda
abstract
  sum-number-of-elements-count-fib :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (count-A : count A) (count-B : count B) →
    Id ( sum-count-ℕ count-B
         ( λ x → number-of-elements-count (count-fib f count-A count-B x)))
       ( number-of-elements-count count-A)
  sum-number-of-elements-count-fib f count-A count-B =
    sum-number-of-elements-count-fiber-count-Σ count-B
      ( count-equiv' (equiv-total-fib f) count-A)

abstract
  double-counting-fib :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (count-A : count A) →
    (count-B : count B) (count-fib-f : (y : B) → count (fib f y)) (y : B) →
    Id ( number-of-elements-count (count-fib-f y))
       ( number-of-elements-count (count-fib f count-A count-B y))
  double-counting-fib f count-A count-B count-fib-f y =
    double-counting (count-fib-f y) (count-fib f count-A count-B y)
```
