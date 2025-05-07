# Tuples on euclidean domains

```agda
module linear-algebra.tuples-on-euclidean-domains where
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

open import linear-algebra.constant-tuples
open import linear-algebra.tuples-on-commutative-rings

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

Given a [Euclidean domain](commutative-algebra.euclidean-domains.md) `R`, the
type `tuple n R` of `R`-[tuples](lists.tuples.md) is an `R`-module.

## Definitions

### Listed tuples on Euclidean domains

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  tuple-Euclidean-Domain : ℕ → UU l
  tuple-Euclidean-Domain = tuple (type-Euclidean-Domain R)

  head-tuple-Euclidean-Domain :
    {n : ℕ} → tuple-Euclidean-Domain (succ-ℕ n) → type-Euclidean-Domain R
  head-tuple-Euclidean-Domain v = head-tuple v

  tail-tuple-Euclidean-Domain :
    {n : ℕ} → tuple-Euclidean-Domain (succ-ℕ n) → tuple-Euclidean-Domain n
  tail-tuple-Euclidean-Domain v = tail-tuple v

  snoc-tuple-Euclidean-Domain :
    {n : ℕ} → tuple-Euclidean-Domain n →
    type-Euclidean-Domain R → tuple-Euclidean-Domain (succ-ℕ n)
  snoc-tuple-Euclidean-Domain v r = snoc-tuple v r
```

### The zero tuple in a Euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-tuple-Euclidean-Domain : {n : ℕ} → tuple-Euclidean-Domain R n
  zero-tuple-Euclidean-Domain = constant-tuple (zero-Euclidean-Domain R)
```

### Pointwise addition of tuples on a Euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-tuple-Euclidean-Domain :
    {n : ℕ} →
    tuple-Euclidean-Domain R n →
    tuple-Euclidean-Domain R n →
    tuple-Euclidean-Domain R n
  add-tuple-Euclidean-Domain = binary-map-tuple (add-Euclidean-Domain R)
```

### Pointwise negation of tuples on a Euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  neg-tuple-Euclidean-Domain :
    {n : ℕ} → tuple-Euclidean-Domain R n → tuple-Euclidean-Domain R n
  neg-tuple-Euclidean-Domain = map-tuple (neg-Euclidean-Domain R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  associative-add-tuple-Euclidean-Domain :
    {n : ℕ} (v1 v2 v3 : tuple-Euclidean-Domain R n) →
    Id
      ( add-tuple-Euclidean-Domain R (add-tuple-Euclidean-Domain R v1 v2) v3)
      ( add-tuple-Euclidean-Domain R v1 (add-tuple-Euclidean-Domain R v2 v3))
  associative-add-tuple-Euclidean-Domain =
    associative-add-tuple-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  left-unit-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id (add-tuple-Euclidean-Domain R (zero-tuple-Euclidean-Domain R) v) v
  left-unit-law-add-tuple-Euclidean-Domain =
    left-unit-law-add-tuple-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  right-unit-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id (add-tuple-Euclidean-Domain R v (zero-tuple-Euclidean-Domain R)) v
  right-unit-law-add-tuple-Euclidean-Domain =
    right-unit-law-add-tuple-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  commutative-add-tuple-Euclidean-Domain :
    {n : ℕ} (v w : tuple-Euclidean-Domain R n) →
    Id (add-tuple-Euclidean-Domain R v w) (add-tuple-Euclidean-Domain R w v)
  commutative-add-tuple-Euclidean-Domain =
    commutative-add-tuple-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### Inverse laws of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  left-inverse-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id
      ( add-tuple-Euclidean-Domain R (neg-tuple-Euclidean-Domain R v) v)
      ( zero-tuple-Euclidean-Domain R)
  left-inverse-law-add-tuple-Euclidean-Domain =
    left-inverse-law-add-tuple-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)

  right-inverse-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id
      ( add-tuple-Euclidean-Domain R v (neg-tuple-Euclidean-Domain R v))
      ( zero-tuple-Euclidean-Domain R)
  right-inverse-law-add-tuple-Euclidean-Domain =
    right-inverse-law-add-tuple-Commutative-Ring
      ( commutative-ring-Euclidean-Domain R)
```

### The abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  tuple-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  tuple-Euclidean-Domain-Semigroup =
    tuple-Commutative-Ring-Semigroup (commutative-ring-Euclidean-Domain R)

  tuple-Euclidean-Domain-Monoid : ℕ → Monoid l
  tuple-Euclidean-Domain-Monoid =
    tuple-Commutative-Ring-Monoid (commutative-ring-Euclidean-Domain R)

  tuple-Euclidean-Domain-Commutative-Monoid : ℕ → Commutative-Monoid l
  tuple-Euclidean-Domain-Commutative-Monoid =
    tuple-Commutative-Ring-Commutative-Monoid
      ( commutative-ring-Euclidean-Domain R)

  tuple-Euclidean-Domain-Group : ℕ → Group l
  tuple-Euclidean-Domain-Group =
    tuple-Commutative-Ring-Group (commutative-ring-Euclidean-Domain R)

  tuple-Euclidean-Domain-Ab : ℕ → Ab l
  tuple-Euclidean-Domain-Ab =
    tuple-Commutative-Ring-Ab (commutative-ring-Euclidean-Domain R)
```
