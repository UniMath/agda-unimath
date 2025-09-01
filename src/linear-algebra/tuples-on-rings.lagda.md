# Tuples on rings

```agda
module linear-algebra.tuples-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-tuples
open import linear-algebra.tuples-on-semirings

open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.rings
```

</details>

## Idea

Given a [ring](ring-theory.rings.md) `R`, the type `tuple n R` of
`R`-[tuples](lists.tuples.md) is an
[abelian group](group-theory.abelian-groups.md).

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where

  tuple-Ring : ℕ → UU l
  tuple-Ring = tuple (type-Ring R)

  head-tuple-Ring : {n : ℕ} → tuple-Ring (succ-ℕ n) → type-Ring R
  head-tuple-Ring v = head-tuple v

  tail-tuple-Ring : {n : ℕ} → tuple-Ring (succ-ℕ n) → tuple-Ring n
  tail-tuple-Ring v = tail-tuple v

  snoc-tuple-Ring : {n : ℕ} → tuple-Ring n → type-Ring R → tuple-Ring (succ-ℕ n)
  snoc-tuple-Ring v r = snoc-tuple v r
```

### The zero tuple in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-tuple-Ring : {n : ℕ} → tuple-Ring R n
  zero-tuple-Ring = constant-tuple (zero-Ring R)
```

### Pointwise addition of tuples in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-tuple-Ring : {n : ℕ} → tuple-Ring R n → tuple-Ring R n → tuple-Ring R n
  add-tuple-Ring = binary-map-tuple (add-Ring R)
```

### Pointwise negation of tuples in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-tuple-Ring : {n : ℕ} → tuple-Ring R n → tuple-Ring R n
  neg-tuple-Ring = map-tuple (neg-Ring R)
```

## Properties of pointwise addition

### Associativity of pointwise addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-tuple-Ring :
    {n : ℕ} (v1 v2 v3 : tuple-Ring R n) →
    Id
      ( add-tuple-Ring R (add-tuple-Ring R v1 v2) v3)
      ( add-tuple-Ring R v1 (add-tuple-Ring R v2 v3))
  associative-add-tuple-Ring = associative-add-tuple-Semiring (semiring-Ring R)
```

### Unit laws of pointwise addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) → Id (add-tuple-Ring R (zero-tuple-Ring R) v) v
  left-unit-law-add-tuple-Ring =
    left-unit-law-add-tuple-Semiring (semiring-Ring R)

  right-unit-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) → Id (add-tuple-Ring R v (zero-tuple-Ring R)) v
  right-unit-law-add-tuple-Ring =
    right-unit-law-add-tuple-Semiring (semiring-Ring R)
```

### Commutativity of pointwise addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-tuple-Ring :
    {n : ℕ} (v w : tuple-Ring R n) →
    add-tuple-Ring R v w ＝ add-tuple-Ring R w v
  commutative-add-tuple-Ring empty-tuple empty-tuple = refl
  commutative-add-tuple-Ring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Ring R x y)
      ( commutative-add-tuple-Ring v w)
```

### Inverse laws of pointwise addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-inverse-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) →
    Id (add-tuple-Ring R (neg-tuple-Ring R v) v) (zero-tuple-Ring R)
  left-inverse-law-add-tuple-Ring empty-tuple = refl
  left-inverse-law-add-tuple-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-inverse-law-add-Ring R x)
      ( left-inverse-law-add-tuple-Ring v)

  right-inverse-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) →
    Id (add-tuple-Ring R v (neg-tuple-Ring R v)) (zero-tuple-Ring R)
  right-inverse-law-add-tuple-Ring empty-tuple = refl
  right-inverse-law-add-tuple-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-inverse-law-add-Ring R x)
      ( right-inverse-law-add-tuple-Ring v)
```

### The abelian group of pointwise addition

```agda
module _
  {l : Level} (R : Ring l)
  where

  tuple-Ring-Semigroup : ℕ → Semigroup l
  tuple-Ring-Semigroup = semigroup-tuple-Semiring (semiring-Ring R)

  tuple-Ring-Monoid : ℕ → Monoid l
  tuple-Ring-Monoid = monoid-tuple-Semiring (semiring-Ring R)

  tuple-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  tuple-Ring-Commutative-Monoid =
    commutative-monoid-tuple-Semiring (semiring-Ring R)

  is-group-tuple-Ring : (n : ℕ) → is-group-Semigroup (tuple-Ring-Semigroup n)
  pr1 (is-group-tuple-Ring n) = is-unital-Monoid (tuple-Ring-Monoid n)
  pr1 (pr2 (is-group-tuple-Ring n)) = neg-tuple-Ring R
  pr1 (pr2 (pr2 (is-group-tuple-Ring n))) = left-inverse-law-add-tuple-Ring R
  pr2 (pr2 (pr2 (is-group-tuple-Ring n))) = right-inverse-law-add-tuple-Ring R

  tuple-Ring-Group : ℕ → Group l
  pr1 (tuple-Ring-Group n) = tuple-Ring-Semigroup n
  pr2 (tuple-Ring-Group n) = is-group-tuple-Ring n

  tuple-Ring-Ab : ℕ → Ab l
  pr1 (tuple-Ring-Ab n) = tuple-Ring-Group n
  pr2 (tuple-Ring-Ab n) = commutative-add-tuple-Ring R
```

## See also

- For the [left module](linear-algebra.left-modules-rings.md) of tuples on
  rings, see
  [`linear-algebra.scalar-multiplication-tuples-on-rings`](linear-algebra.scalar-multiplication-tuples-on-rings.md)
