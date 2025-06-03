# Finite sequences in euclidean domains

```agda
module linear-algebra.finite-sequences-in-euclidean-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.euclidean-domains

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-commutative-rings

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
```

</details>

## Idea

Given a [Euclidean domain](commutative-algebra.euclidean-domains.md) `R`, the
type `fin-sequence n R` of `R`-[finite sequences](lists.finite-sequences.md) is
an `R`-module.

## Definitions

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  fin-sequence-type-Euclidean-Domain : ℕ → UU l
  fin-sequence-type-Euclidean-Domain = fin-sequence (type-Euclidean-Domain R)

  head-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) →
    fin-sequence-type-Euclidean-Domain (succ-ℕ n) →
    type-Euclidean-Domain R
  head-fin-sequence-type-Euclidean-Domain n v = head-fin-sequence n v

  tail-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) →
    fin-sequence-type-Euclidean-Domain (succ-ℕ n) →
    fin-sequence-type-Euclidean-Domain n
  tail-fin-sequence-type-Euclidean-Domain = tail-fin-sequence

  cons-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) → type-Euclidean-Domain R →
    fin-sequence-type-Euclidean-Domain n →
    fin-sequence-type-Euclidean-Domain (succ-ℕ n)
  cons-fin-sequence-type-Euclidean-Domain = cons-fin-sequence

  snoc-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) → fin-sequence-type-Euclidean-Domain n → type-Euclidean-Domain R →
    fin-sequence-type-Euclidean-Domain (succ-ℕ n)
  snoc-fin-sequence-type-Euclidean-Domain = snoc-fin-sequence
```

### The zero finite sequence in a Euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) → fin-sequence-type-Euclidean-Domain R n
  zero-fin-sequence-type-Euclidean-Domain n i = zero-Euclidean-Domain R
```

### Pointwise addition of finite sequences in a Euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) (v w : fin-sequence-type-Euclidean-Domain R n) →
    fin-sequence-type-Euclidean-Domain R n
  add-fin-sequence-type-Euclidean-Domain n =
    binary-map-fin-sequence n (add-Euclidean-Domain R)
```

### Pointwise negation of finite sequences on a Euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  neg-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) → fin-sequence-type-Euclidean-Domain R n →
    fin-sequence-type-Euclidean-Domain R n
  neg-fin-sequence-type-Euclidean-Domain =
    neg-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  associative-add-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Euclidean-Domain R n) →
    ( add-fin-sequence-type-Euclidean-Domain
      ( R)
      ( n)
      ( add-fin-sequence-type-Euclidean-Domain R n v1 v2)
      ( v3)) ＝
    ( add-fin-sequence-type-Euclidean-Domain
      ( R)
      ( n)
      ( v1)
      ( add-fin-sequence-type-Euclidean-Domain R n v2 v3))
  associative-add-fin-sequence-type-Euclidean-Domain =
    associative-add-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  left-unit-law-add-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-type-Euclidean-Domain R n) →
    ( add-fin-sequence-type-Euclidean-Domain
      ( R)
      ( n)
      ( zero-fin-sequence-type-Euclidean-Domain R n)
      ( v)) ＝
    ( v)
  left-unit-law-add-fin-sequence-type-Euclidean-Domain =
    left-unit-law-add-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  right-unit-law-add-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-type-Euclidean-Domain R n) →
    ( add-fin-sequence-type-Euclidean-Domain
      ( R)
      ( n)
      ( v)
      ( zero-fin-sequence-type-Euclidean-Domain R n)) ＝
    ( v)
  right-unit-law-add-fin-sequence-type-Euclidean-Domain =
    right-unit-law-add-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  commutative-add-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) (v w : fin-sequence-type-Euclidean-Domain R n) →
    add-fin-sequence-type-Euclidean-Domain R n v w ＝
    add-fin-sequence-type-Euclidean-Domain R n w v
  commutative-add-fin-sequence-type-Euclidean-Domain =
    commutative-add-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Inverse laws of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  left-inverse-law-add-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-type-Euclidean-Domain R n) →
    Id
      ( add-fin-sequence-type-Euclidean-Domain
        R n ( neg-fin-sequence-type-Euclidean-Domain R n v) v)
      ( zero-fin-sequence-type-Euclidean-Domain R n)
  left-inverse-law-add-fin-sequence-type-Euclidean-Domain =
    left-inverse-law-add-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  right-inverse-law-add-fin-sequence-type-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-type-Euclidean-Domain R n) →
    Id
      ( add-fin-sequence-type-Euclidean-Domain
        ( R)
        ( n)
        ( v)
        ( neg-fin-sequence-type-Euclidean-Domain R n v))
      ( zero-fin-sequence-type-Euclidean-Domain R n)
  right-inverse-law-add-fin-sequence-type-Euclidean-Domain =
    right-inverse-law-add-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### The abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  semigroup-fin-sequence-type-Euclidean-Domain : ℕ → Semigroup l
  semigroup-fin-sequence-type-Euclidean-Domain =
    semigroup-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  monoid-fin-sequence-type-Euclidean-Domain : ℕ → Monoid l
  monoid-fin-sequence-type-Euclidean-Domain =
    monoid-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  commutative-monoid-fin-sequence-type-Euclidean-Domain :
    ℕ → Commutative-Monoid l
  commutative-monoid-fin-sequence-type-Euclidean-Domain =
    commutative-monoid-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  group-fin-sequence-type-Euclidean-Domain : ℕ → Group l
  group-fin-sequence-type-Euclidean-Domain =
    group-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  ab-fin-sequence-type-Euclidean-Domain : ℕ → Ab l
  ab-fin-sequence-type-Euclidean-Domain =
    ab-fin-sequence-type-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```
