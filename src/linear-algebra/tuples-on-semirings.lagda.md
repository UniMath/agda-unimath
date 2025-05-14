# Tuples on semirings

```agda
module linear-algebra.tuples-on-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-tuples

open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.semirings
```

</details>

## Idea

Given a [semiring](ring-theory.semirings.md) `R`, the type `tuple n R` of
`R`-[tuples](lists.tuples.md) is a
[commutative monoid](group-theory.commutative-monoids.md) under addition.

## Definitions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  tuple-Semiring : ℕ → UU l
  tuple-Semiring = tuple (type-Semiring R)

  head-tuple-Semiring : {n : ℕ} → tuple-Semiring (succ-ℕ n) → type-Semiring R
  head-tuple-Semiring v = head-tuple v

  tail-tuple-Semiring : {n : ℕ} → tuple-Semiring (succ-ℕ n) → tuple-Semiring n
  tail-tuple-Semiring v = tail-tuple v

  snoc-tuple-Semiring :
    {n : ℕ} → tuple-Semiring n → type-Semiring R → tuple-Semiring (succ-ℕ n)
  snoc-tuple-Semiring v r = snoc-tuple v r
```

### The zero tuple in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-tuple-Semiring : {n : ℕ} → tuple-Semiring R n
  zero-tuple-Semiring = constant-tuple (zero-Semiring R)
```

### Pointwise addition of tuples in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-tuple-Semiring :
    {n : ℕ} → tuple-Semiring R n → tuple-Semiring R n → tuple-Semiring R n
  add-tuple-Semiring = binary-map-tuple (add-Semiring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  associative-add-tuple-Semiring :
    {n : ℕ} (v1 v2 v3 : tuple-Semiring R n) →
    add-tuple-Semiring R (add-tuple-Semiring R v1 v2) v3 ＝
    add-tuple-Semiring R v1 (add-tuple-Semiring R v2 v3)
  associative-add-tuple-Semiring empty-tuple empty-tuple empty-tuple = refl
  associative-add-tuple-Semiring (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Semiring R x y z)
      ( associative-add-tuple-Semiring v1 v2 v3)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-unit-law-add-tuple-Semiring :
    {n : ℕ} (v : tuple-Semiring R n) →
    add-tuple-Semiring R (zero-tuple-Semiring R) v ＝ v
  left-unit-law-add-tuple-Semiring empty-tuple = refl
  left-unit-law-add-tuple-Semiring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Semiring R x)
      ( left-unit-law-add-tuple-Semiring v)

  right-unit-law-add-tuple-Semiring :
    {n : ℕ} (v : tuple-Semiring R n) →
    add-tuple-Semiring R v (zero-tuple-Semiring R) ＝ v
  right-unit-law-add-tuple-Semiring empty-tuple = refl
  right-unit-law-add-tuple-Semiring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Semiring R x)
      ( right-unit-law-add-tuple-Semiring v)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  commutative-add-tuple-Semiring :
    {n : ℕ} (v w : tuple-Semiring R n) →
    add-tuple-Semiring R v w ＝ add-tuple-Semiring R w v
  commutative-add-tuple-Semiring empty-tuple empty-tuple = refl
  commutative-add-tuple-Semiring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Semiring R x y)
      ( commutative-add-tuple-Semiring v w)
```

### The commutative monoid of pointwise addition

```agda
module _
  {l : Level} (R : Semiring l)
  where

  tuple-Semiring-Semigroup : ℕ → Semigroup l
  pr1 (tuple-Semiring-Semigroup n) = tuple-Set (set-Semiring R) n
  pr1 (pr2 (tuple-Semiring-Semigroup n)) = add-tuple-Semiring R
  pr2 (pr2 (tuple-Semiring-Semigroup n)) = associative-add-tuple-Semiring R

  tuple-Semiring-Monoid : ℕ → Monoid l
  pr1 (tuple-Semiring-Monoid n) = tuple-Semiring-Semigroup n
  pr1 (pr2 (tuple-Semiring-Monoid n)) = zero-tuple-Semiring R
  pr1 (pr2 (pr2 (tuple-Semiring-Monoid n))) = left-unit-law-add-tuple-Semiring R
  pr2 (pr2 (pr2 (tuple-Semiring-Monoid n))) =
    right-unit-law-add-tuple-Semiring R

  tuple-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (tuple-Semiring-Commutative-Monoid n) = tuple-Semiring-Monoid n
  pr2 (tuple-Semiring-Commutative-Monoid n) = commutative-add-tuple-Semiring R
```
