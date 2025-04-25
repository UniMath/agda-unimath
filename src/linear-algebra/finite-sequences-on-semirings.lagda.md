# Finite sequences on semirings

```agda
module linear-algebra.finite-sequences-on-semirings where
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
`finite-sequence-Semiring R n` of
`R`-[finite sequences](lists.finite-sequences.md) is a
[commutative monoid](group-theory.commutative-monoids.md) under addition.

## Definitions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  fin-sequence-Semiring : ℕ → UU l
  fin-sequence-Semiring = fin-sequence (type-Semiring R)

  head-fin-sequence-Semiring :
    (n : ℕ) → fin-sequence-Semiring (succ-ℕ n) → type-Semiring R
  head-fin-sequence-Semiring n v = head-fin-sequence n v

  tail-fin-sequence-Semiring :
    (n : ℕ) → fin-sequence-Semiring (succ-ℕ n) → fin-sequence-Semiring n
  tail-fin-sequence-Semiring = tail-fin-sequence

  cons-fin-sequence-Semiring :
    (n : ℕ) → type-Semiring R →
    fin-sequence-Semiring n → fin-sequence-Semiring (succ-ℕ n)
  cons-fin-sequence-Semiring = cons-fin-sequence

  snoc-fin-sequence-Semiring :
    (n : ℕ) → fin-sequence-Semiring n → type-Semiring R →
    fin-sequence-Semiring (succ-ℕ n)
  snoc-fin-sequence-Semiring = snoc-fin-sequence
```

### Zero finite sequence on a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-fin-sequence-Semiring : (n : ℕ) → fin-sequence-Semiring R n
  zero-fin-sequence-Semiring n i = zero-Semiring R
```

### Pointwise addition on a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-fin-sequence-Semiring :
    (n : ℕ) (v w : fin-sequence-Semiring R n) →
    fin-sequence-Semiring R n
  add-fin-sequence-Semiring n =
    binary-map-fin-sequence n (add-Semiring R)
```

## Properties

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  associative-add-fin-sequence-Semiring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-Semiring R n) →
    ( add-fin-sequence-Semiring R
      ( n)
      ( add-fin-sequence-Semiring R n v1 v2)
      ( v3)) ＝
    ( add-fin-sequence-Semiring R
      ( n)
      ( v1)
      ( add-fin-sequence-Semiring R n v2 v3))
  associative-add-fin-sequence-Semiring n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Semiring R (v1 i) (v2 i) (v3 i))
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-unit-law-add-fin-sequence-Semiring :
    (n : ℕ) (v : fin-sequence-Semiring R n) →
    add-fin-sequence-Semiring R n (zero-fin-sequence-Semiring R n) v ＝ v
  left-unit-law-add-fin-sequence-Semiring n v =
    eq-htpy (λ i → left-unit-law-add-Semiring R (v i))

  right-unit-law-add-fin-sequence-Semiring :
    (n : ℕ) (v : fin-sequence-Semiring R n) →
    add-fin-sequence-Semiring R n v (zero-fin-sequence-Semiring R n) ＝ v
  right-unit-law-add-fin-sequence-Semiring n v =
    eq-htpy (λ i → right-unit-law-add-Semiring R (v i))
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  commutative-add-fin-sequence-Semiring :
    (n : ℕ) (v w : fin-sequence-Semiring R n) →
    add-fin-sequence-Semiring R n v w ＝ add-fin-sequence-Semiring R n w v
  commutative-add-fin-sequence-Semiring n v w =
    eq-htpy (λ i → commutative-add-Semiring R (v i) (w i))
```

### Commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  fin-sequence-Semiring-Semigroup : ℕ → Semigroup l
  pr1 (fin-sequence-Semiring-Semigroup n) =
    fin-sequence-Set (set-Semiring R) n
  pr1 (pr2 (fin-sequence-Semiring-Semigroup n)) =
    add-fin-sequence-Semiring R n
  pr2 (pr2 (fin-sequence-Semiring-Semigroup n)) =
    associative-add-fin-sequence-Semiring R n

  fin-sequence-Semiring-Monoid : ℕ → Monoid l
  pr1 (fin-sequence-Semiring-Monoid n) =
    fin-sequence-Semiring-Semigroup n
  pr1 (pr2 (fin-sequence-Semiring-Monoid n)) =
    zero-fin-sequence-Semiring R n
  pr1 (pr2 (pr2 (fin-sequence-Semiring-Monoid n))) =
    left-unit-law-add-fin-sequence-Semiring R n
  pr2 (pr2 (pr2 (fin-sequence-Semiring-Monoid n))) =
    right-unit-law-add-fin-sequence-Semiring R n

  fin-sequence-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (fin-sequence-Semiring-Commutative-Monoid n) =
    fin-sequence-Semiring-Monoid n
  pr2 (fin-sequence-Semiring-Commutative-Monoid n) =
    commutative-add-fin-sequence-Semiring R n
```
