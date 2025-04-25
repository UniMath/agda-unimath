# Finite sequences on euclidean domains

```agda
module linear-algebra.finite-sequences-on-euclidean-domains where
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

open import linear-algebra.finite-sequences-on-commutative-rings

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
```

</details>

## Idea

Given an [Euclidean domain](commutative-algebra.euclidean-domains.md) `R`, the
type `fin-sequence n R` of `R`-[finite sequences](lists.finite-sequences.md) is
an `R`-module.

## Definitions

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  fin-sequence-Euclidean-Domain : ℕ → UU l
  fin-sequence-Euclidean-Domain = fin-sequence (type-Euclidean-Domain R)

  head-fin-sequence-Euclidean-Domain :
    (n : ℕ) →
    fin-sequence-Euclidean-Domain (succ-ℕ n) →
    type-Euclidean-Domain R
  head-fin-sequence-Euclidean-Domain n v = head-fin-sequence n v

  tail-fin-sequence-Euclidean-Domain :
    (n : ℕ) →
    fin-sequence-Euclidean-Domain (succ-ℕ n) →
    fin-sequence-Euclidean-Domain n
  tail-fin-sequence-Euclidean-Domain = tail-fin-sequence

  cons-fin-sequence-Euclidean-Domain :
    (n : ℕ) → type-Euclidean-Domain R →
    fin-sequence-Euclidean-Domain n →
    fin-sequence-Euclidean-Domain (succ-ℕ n)
  cons-fin-sequence-Euclidean-Domain = cons-fin-sequence

  snoc-fin-sequence-Euclidean-Domain :
    (n : ℕ) → fin-sequence-Euclidean-Domain n → type-Euclidean-Domain R →
    fin-sequence-Euclidean-Domain (succ-ℕ n)
  snoc-fin-sequence-Euclidean-Domain = snoc-fin-sequence
```

### Zero finite sequences on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-fin-sequence-Euclidean-Domain :
    (n : ℕ) → fin-sequence-Euclidean-Domain R n
  zero-fin-sequence-Euclidean-Domain n i = zero-Euclidean-Domain R
```

### Pointwise addition of finite sequences on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-fin-sequence-Euclidean-Domain :
    (n : ℕ) (v w : fin-sequence-Euclidean-Domain R n) →
    fin-sequence-Euclidean-Domain R n
  add-fin-sequence-Euclidean-Domain n =
    binary-map-fin-sequence n (add-Euclidean-Domain R)
```

### Pointwise negation of finite sequences on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  neg-fin-sequence-Euclidean-Domain :
    (n : ℕ) → fin-sequence-Euclidean-Domain R n →
    fin-sequence-Euclidean-Domain R n
  neg-fin-sequence-Euclidean-Domain =
    neg-fin-sequence-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

## Properties of pointwise addition

### Associativity

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  associative-add-fin-sequence-Euclidean-Domain :
    (n : ℕ) (v1 v2 v3 : fin-sequence-Euclidean-Domain R n) →
    ( add-fin-sequence-Euclidean-Domain
      ( R)
      ( n)
      ( add-fin-sequence-Euclidean-Domain R n v1 v2)
      ( v3)) ＝
    ( add-fin-sequence-Euclidean-Domain
      ( R)
      ( n)
      ( v1)
      ( add-fin-sequence-Euclidean-Domain R n v2 v3))
  associative-add-fin-sequence-Euclidean-Domain =
    associative-add-fin-sequence-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Unit laws

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  left-unit-law-add-fin-sequence-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-Euclidean-Domain R n) →
    ( add-fin-sequence-Euclidean-Domain
      ( R)
      ( n)
      ( zero-fin-sequence-Euclidean-Domain R n)
      ( v)) ＝
    ( v)
  left-unit-law-add-fin-sequence-Euclidean-Domain =
    left-unit-law-add-fin-sequence-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  right-unit-law-add-fin-sequence-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-Euclidean-Domain R n) →
    ( add-fin-sequence-Euclidean-Domain
      ( R)
      ( n)
      ( v)
      ( zero-fin-sequence-Euclidean-Domain R n)) ＝
    ( v)
  right-unit-law-add-fin-sequence-Euclidean-Domain =
    right-unit-law-add-fin-sequence-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Commutativity

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  commutative-add-fin-sequence-Euclidean-Domain :
    (n : ℕ) (v w : fin-sequence-Euclidean-Domain R n) →
    add-fin-sequence-Euclidean-Domain R n v w ＝
    add-fin-sequence-Euclidean-Domain R n w v
  commutative-add-fin-sequence-Euclidean-Domain =
    commutative-add-fin-sequence-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Inverse laws

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  left-inverse-law-add-fin-sequence-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-Euclidean-Domain R n) →
    Id
      ( add-fin-sequence-Euclidean-Domain
        R n ( neg-fin-sequence-Euclidean-Domain R n v) v)
      ( zero-fin-sequence-Euclidean-Domain R n)
  left-inverse-law-add-fin-sequence-Euclidean-Domain =
    left-inverse-law-add-fin-sequence-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  right-inverse-law-add-fin-sequence-Euclidean-Domain :
    (n : ℕ) (v : fin-sequence-Euclidean-Domain R n) →
    Id
      ( add-fin-sequence-Euclidean-Domain
        ( R)
        ( n)
        ( v)
        ( neg-fin-sequence-Euclidean-Domain R n v))
      ( zero-fin-sequence-Euclidean-Domain R n)
  right-inverse-law-add-fin-sequence-Euclidean-Domain =
    right-inverse-law-add-fin-sequence-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  fin-sequence-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  fin-sequence-Euclidean-Domain-Semigroup =
    fin-sequence-Commutative-Ring-Semigroup
      ( commutative-ring-Euclidean-Domain R)

  fin-sequence-Euclidean-Domain-Monoid : ℕ → Monoid l
  fin-sequence-Euclidean-Domain-Monoid =
    fin-sequence-Commutative-Ring-Monoid
      ( commutative-ring-Euclidean-Domain R)

  fin-sequence-Euclidean-Domain-Commutative-Monoid : ℕ → Commutative-Monoid l
  fin-sequence-Euclidean-Domain-Commutative-Monoid =
    fin-sequence-Commutative-Ring-Commutative-Monoid
      ( commutative-ring-Euclidean-Domain R)

  fin-sequence-Euclidean-Domain-Group : ℕ → Group l
  fin-sequence-Euclidean-Domain-Group =
    fin-sequence-Commutative-Ring-Group
      ( commutative-ring-Euclidean-Domain R)

  fin-sequence-Euclidean-Domain-Ab : ℕ → Ab l
  fin-sequence-Euclidean-Domain-Ab =
    fin-sequence-Commutative-Ring-Ab
      ( commutative-ring-Euclidean-Domain R)
```
