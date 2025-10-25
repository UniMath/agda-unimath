# Finite sequences in monoids

```agda
module linear-algebra.finite-sequences-in-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-semigroups

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
```

</details>

## Idea

Given a [monoid](group-theory.monoids.md) `M`, the type `fin-sequence n M` of
[finite sequences](lists.finite-sequences.md) of length `n` of elements of `M`
is a monoid given by componentwise multiplication.

We use additive terminology for finite sequences, as is standard in linear
algebra contexts, despite using multiplicative terminology for monoids.

## Definitions

```agda
module _
  {l : Level} (M : Monoid l)
  where

  fin-sequence-type-Monoid : ℕ → UU l
  fin-sequence-type-Monoid = fin-sequence (type-Monoid M)

  head-fin-sequence-type-Monoid :
    (n : ℕ) → fin-sequence-type-Monoid (succ-ℕ n) → type-Monoid M
  head-fin-sequence-type-Monoid n v = head-fin-sequence n v

  tail-fin-sequence-type-Monoid :
    (n : ℕ) → fin-sequence-type-Monoid (succ-ℕ n) → fin-sequence-type-Monoid n
  tail-fin-sequence-type-Monoid = tail-fin-sequence

  cons-fin-sequence-type-Monoid :
    (n : ℕ) → type-Monoid M →
    fin-sequence-type-Monoid n → fin-sequence-type-Monoid (succ-ℕ n)
  cons-fin-sequence-type-Monoid = cons-fin-sequence

  snoc-fin-sequence-type-Monoid :
    (n : ℕ) → fin-sequence-type-Monoid n → type-Monoid M →
    fin-sequence-type-Monoid (succ-ℕ n)
  snoc-fin-sequence-type-Monoid = snoc-fin-sequence
```

### The finite sequence of zeros in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  zero-fin-sequence-type-Monoid : (n : ℕ) → fin-sequence-type-Monoid M n
  zero-fin-sequence-type-Monoid n i = unit-Monoid M
```

### Pointwise addition of finite sequences in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  add-fin-sequence-type-Monoid :
    (n : ℕ) (v w : fin-sequence-type-Monoid M n) → fin-sequence-type-Monoid M n
  add-fin-sequence-type-Monoid n = binary-map-fin-sequence n (mul-Monoid M)

  associative-add-fin-sequence-type-Monoid :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Monoid M n) →
    add-fin-sequence-type-Monoid n (add-fin-sequence-type-Monoid n v1 v2) v3 ＝
    ( add-fin-sequence-type-Monoid n v1 (add-fin-sequence-type-Monoid n v2 v3))
  associative-add-fin-sequence-type-Monoid =
    associative-add-fin-sequence-type-Semigroup (semigroup-Monoid M)

  semigroup-fin-sequence-type-Monoid : ℕ → Semigroup l
  semigroup-fin-sequence-type-Monoid =
    semigroup-fin-sequence-type-Semigroup (semigroup-Monoid M)

  left-unit-law-add-fin-sequence-type-Monoid :
    (n : ℕ) (v : fin-sequence-type-Monoid M n) →
    add-fin-sequence-type-Monoid n (zero-fin-sequence-type-Monoid M n) v ＝ v
  left-unit-law-add-fin-sequence-type-Monoid n v =
    eq-htpy (λ i → left-unit-law-mul-Monoid M (v i))

  right-unit-law-add-fin-sequence-type-Monoid :
    (n : ℕ) (v : fin-sequence-type-Monoid M n) →
    add-fin-sequence-type-Monoid n v (zero-fin-sequence-type-Monoid M n) ＝ v
  right-unit-law-add-fin-sequence-type-Monoid n v =
    eq-htpy (λ i → right-unit-law-mul-Monoid M (v i))

  monoid-fin-sequence-type-Monoid : ℕ → Monoid l
  pr1 (monoid-fin-sequence-type-Monoid n) =
    semigroup-fin-sequence-type-Monoid n
  pr1 (pr2 (monoid-fin-sequence-type-Monoid n)) =
    zero-fin-sequence-type-Monoid M n
  pr1 (pr2 (pr2 (monoid-fin-sequence-type-Monoid n))) =
    left-unit-law-add-fin-sequence-type-Monoid n
  pr2 (pr2 (pr2 (monoid-fin-sequence-type-Monoid n))) =
    right-unit-law-add-fin-sequence-type-Monoid n
```
