# Repetitions of values

```agda
module univalent-combinatorics.repetitions-of-values where

open import foundation.repetitions-of-values public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types

open import foundation.cartesian-product-types
open import foundation.decidable-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.noninjective-maps
open import foundation.pairs-of-distinct-elements
open import foundation.sets

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **repetition of values** of a map `f : A → B` consists of a
[pair of distinct elements](foundation.pairs-of-distinct-elements.md) `x ≠ y` of
`A` that get mapped to the [same](foundation-core.identity-types.md) element in
`B`: `f x ＝ f y`.

## Properties

### If `f : Fin k → Fin l` is not injective, then it has a repetition of values

```agda
repetition-of-values-is-not-injective-Fin :
  (k l : ℕ) (f : Fin k → Fin l) →
  is-not-injective f → repetition-of-values f
repetition-of-values-is-not-injective-Fin k l f N =
  pair (pair x (pair y (pr2 w))) (pr1 w)
  where
  u : Σ (Fin k) (λ x → ¬ ((y : Fin k) → f x ＝ f y → x ＝ y))
  u =
    exists-not-not-for-all-Fin k
      ( λ x →
        is-decidable-Π-Fin k
          ( λ y →
            is-decidable-function-type
              ( has-decidable-equality-Fin l (f x) (f y))
              ( has-decidable-equality-Fin k x y)))
      ( λ f → N (λ {x} {y} → f x y))
  x : Fin k
  x = pr1 u
  H : ¬ ((y : Fin k) → f x ＝ f y → x ＝ y)
  H = pr2 u
  v : Σ (Fin k) (λ y → ¬ (f x ＝ f y → x ＝ y))
  v = exists-not-not-for-all-Fin k
      ( λ y →
        is-decidable-function-type
          ( has-decidable-equality-Fin l (f x) (f y))
          ( has-decidable-equality-Fin k x y))
      ( H)
  y : Fin k
  y = pr1 v
  K : ¬ (f x ＝ f y → x ＝ y)
  K = pr2 v
  w : (f x ＝ f y) × (x ≠ y)
  w = exists-not-not-for-all-count
      ( λ _ → Id x y)
      ( λ _ →
        has-decidable-equality-Fin k x y)
      ( count-is-decidable-is-prop
        ( is-set-Fin l (f x) (f y))
        ( has-decidable-equality-Fin l (f x) (f y)))
      ( K)
```

> **Comment.** We could modify this construction to provide proof that `i < j`
> rather than `i ≠ j`.

### On the standard finite sets, we can count the number of pairs of distinct elements

```agda
count-pair-of-distinct-elements-Fin :
  (k : ℕ) → count (pair-of-distinct-elements (Fin k))
count-pair-of-distinct-elements-Fin k =
  count-Σ-Fin k
    ( λ x →
      count-decidable-subtype-Fin k
        ( λ y → neg-Decidable-Prop (decidable-Eq-Fin k x y)))
```

### On the standard finite sets, `is-repeated-value f x` is decidable

```agda
is-decidable-is-repeated-value-Fin :
  (k l : ℕ) (f : Fin k → Fin l) (x : Fin k) →
  is-decidable (is-repeated-value f x)
is-decidable-is-repeated-value-Fin k l f x =
  is-decidable-Σ-count
    ( count-decidable-subtype-Fin k
      ( λ y → neg-Decidable-Prop (decidable-Eq-Fin k x y)))
    ( λ (y , p) → has-decidable-equality-Fin l (f x) (f y))
```

### On the standard finite sets, `repetition-of-values f` is decidable

```agda
is-decidable-repetition-of-values-Fin :
  (k l : ℕ) (f : Fin k → Fin l) → is-decidable (repetition-of-values f)
is-decidable-repetition-of-values-Fin k l f =
  is-decidable-Σ-count
    ( count-pair-of-distinct-elements-Fin k)
    ( λ (x , y , _) → has-decidable-equality-Fin l (f x) (f y))
```

## See also

- [The pigeonhole principle](univalent-combinatorics.pigeonhole-principle.md)
