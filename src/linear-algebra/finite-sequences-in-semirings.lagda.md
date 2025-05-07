# Finite sequences in semirings

```agda
module linear-algebra.finite-sequences-in-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import ring-theory.semirings
```

</details>

## Idea

Given a [semiring](ring-theory.semirings.md) `R`, the type
`finite-sequence-Semiring R n` of [finite sequences](lists.finite-sequences.md)
of length `n` in the underlying type of `R` is a
[commutative monoid](group-theory.commutative-monoids.md) under addition.

## Definitions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  fin-sequence-type-Semiring : ℕ → UU l
  fin-sequence-type-Semiring = fin-sequence (type-Semiring R)

  head-fin-sequence-type-Semiring :
    (n : ℕ) → fin-sequence-type-Semiring (succ-ℕ n) → type-Semiring R
  head-fin-sequence-type-Semiring n v = head-fin-sequence n v

  tail-fin-sequence-type-Semiring :
    (n : ℕ) → fin-sequence-type-Semiring (succ-ℕ n) →
    fin-sequence-type-Semiring n
  tail-fin-sequence-type-Semiring = tail-fin-sequence

  cons-fin-sequence-type-Semiring :
    (n : ℕ) → type-Semiring R →
    fin-sequence-type-Semiring n → fin-sequence-type-Semiring (succ-ℕ n)
  cons-fin-sequence-type-Semiring = cons-fin-sequence

  snoc-fin-sequence-type-Semiring :
    (n : ℕ) → fin-sequence-type-Semiring n → type-Semiring R →
    fin-sequence-type-Semiring (succ-ℕ n)
  snoc-fin-sequence-type-Semiring = snoc-fin-sequence
```

### The zero finite sequence in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-fin-sequence-type-Semiring : (n : ℕ) → fin-sequence-type-Semiring R n
  zero-fin-sequence-type-Semiring n i = zero-Semiring R
```

### Pointwise addition of finite sequences in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-fin-sequence-type-Semiring :
    (n : ℕ) (v w : fin-sequence-type-Semiring R n) →
    fin-sequence-type-Semiring R n
  add-fin-sequence-type-Semiring n =
    binary-map-fin-sequence n (add-Semiring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  associative-add-fin-sequence-type-Semiring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Semiring R n) →
    ( add-fin-sequence-type-Semiring R
      ( n)
      ( add-fin-sequence-type-Semiring R n v1 v2)
      ( v3)) ＝
    ( add-fin-sequence-type-Semiring R
      ( n)
      ( v1)
      ( add-fin-sequence-type-Semiring R n v2 v3))
  associative-add-fin-sequence-type-Semiring n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Semiring R (v1 i) (v2 i) (v3 i))
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-unit-law-add-fin-sequence-type-Semiring :
    (n : ℕ) (v : fin-sequence-type-Semiring R n) →
    add-fin-sequence-type-Semiring R n
      ( zero-fin-sequence-type-Semiring R n)
      ( v) ＝
    v
  left-unit-law-add-fin-sequence-type-Semiring n v =
    eq-htpy (λ i → left-unit-law-add-Semiring R (v i))

  right-unit-law-add-fin-sequence-type-Semiring :
    (n : ℕ) (v : fin-sequence-type-Semiring R n) →
    add-fin-sequence-type-Semiring R n
      ( v)
      ( zero-fin-sequence-type-Semiring R n) ＝
    v
  right-unit-law-add-fin-sequence-type-Semiring n v =
    eq-htpy (λ i → right-unit-law-add-Semiring R (v i))
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  commutative-add-fin-sequence-type-Semiring :
    (n : ℕ) (v w : fin-sequence-type-Semiring R n) →
    add-fin-sequence-type-Semiring R n v w ＝
    add-fin-sequence-type-Semiring R n w v
  commutative-add-fin-sequence-type-Semiring n v w =
    eq-htpy (λ i → commutative-add-Semiring R (v i) (w i))
```

### The commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  semigroup-fin-sequence-type-Semiring : ℕ → Semigroup l
  pr1 (semigroup-fin-sequence-type-Semiring n) =
    fin-sequence-Set (set-Semiring R) n
  pr1 (pr2 (semigroup-fin-sequence-type-Semiring n)) =
    add-fin-sequence-type-Semiring R n
  pr2 (pr2 (semigroup-fin-sequence-type-Semiring n)) =
    associative-add-fin-sequence-type-Semiring R n

  monoid-fin-sequence-type-Semiring : ℕ → Monoid l
  pr1 (monoid-fin-sequence-type-Semiring n) =
    semigroup-fin-sequence-type-Semiring n
  pr1 (pr2 (monoid-fin-sequence-type-Semiring n)) =
    zero-fin-sequence-type-Semiring R n
  pr1 (pr2 (pr2 (monoid-fin-sequence-type-Semiring n))) =
    left-unit-law-add-fin-sequence-type-Semiring R n
  pr2 (pr2 (pr2 (monoid-fin-sequence-type-Semiring n))) =
    right-unit-law-add-fin-sequence-type-Semiring R n

  commutative-monoid-fin-sequence-type-Semiring : ℕ → Commutative-Monoid l
  pr1 (commutative-monoid-fin-sequence-type-Semiring n) =
    monoid-fin-sequence-type-Semiring n
  pr2 (commutative-monoid-fin-sequence-type-Semiring n) =
    commutative-add-fin-sequence-type-Semiring R n
```
