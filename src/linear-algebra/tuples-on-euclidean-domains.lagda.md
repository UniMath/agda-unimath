# Tuples on euclidean domains

```agda
module linear-algebra.tuples-on-euclidean-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.euclidean-domains

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.constant-tuples
open import linear-algebra.functoriality-tuples
open import linear-algebra.tuples
```

</details>

## Idea

Given an [Euclidean domain](commutative-algebra.euclidean-domains.md) `R`, the
type `tuple n R` of `R`-[tuples](linear-algebra.tuples.md) is an `R`-module.

## Definitions

### Listed tuples on euclidean domains

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

### Functional tuples on euclidean domains

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  functional-tuple-Euclidean-Domain : ℕ → UU l
  functional-tuple-Euclidean-Domain = functional-tuple (type-Euclidean-Domain R)

  head-functional-tuple-Euclidean-Domain :
    (n : ℕ) →
    functional-tuple-Euclidean-Domain (succ-ℕ n) →
    type-Euclidean-Domain R
  head-functional-tuple-Euclidean-Domain n v = head-functional-tuple n v

  tail-functional-tuple-Euclidean-Domain :
    (n : ℕ) →
    functional-tuple-Euclidean-Domain (succ-ℕ n) →
    functional-tuple-Euclidean-Domain n
  tail-functional-tuple-Euclidean-Domain = tail-functional-tuple

  cons-functional-tuple-Euclidean-Domain :
    (n : ℕ) → type-Euclidean-Domain R →
    functional-tuple-Euclidean-Domain n →
    functional-tuple-Euclidean-Domain (succ-ℕ n)
  cons-functional-tuple-Euclidean-Domain = cons-functional-tuple

  snoc-functional-tuple-Euclidean-Domain :
    (n : ℕ) → functional-tuple-Euclidean-Domain n → type-Euclidean-Domain R →
    functional-tuple-Euclidean-Domain (succ-ℕ n)
  snoc-functional-tuple-Euclidean-Domain = snoc-functional-tuple
```

### Zero tuple on a euclidean domain

#### The zero listed tuple

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-tuple-Euclidean-Domain : {n : ℕ} → tuple-Euclidean-Domain R n
  zero-tuple-Euclidean-Domain = constant-tuple (zero-Euclidean-Domain R)
```

#### The zero functional tuple

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-functional-tuple-Euclidean-Domain :
    (n : ℕ) → functional-tuple-Euclidean-Domain R n
  zero-functional-tuple-Euclidean-Domain n i = zero-Euclidean-Domain R
```

### Pointwise addition of tuples on a euclidean domain

#### Pointwise addition of listed tuples on a euclidean domain

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

  associative-add-tuple-Euclidean-Domain :
    {n : ℕ} (v1 v2 v3 : tuple-Euclidean-Domain R n) →
    Id
      ( add-tuple-Euclidean-Domain (add-tuple-Euclidean-Domain v1 v2) v3)
      ( add-tuple-Euclidean-Domain v1 (add-tuple-Euclidean-Domain v2 v3))
  associative-add-tuple-Euclidean-Domain empty-tuple empty-tuple empty-tuple =
    refl
  associative-add-tuple-Euclidean-Domain (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Euclidean-Domain R x y z)
      ( associative-add-tuple-Euclidean-Domain v1 v2 v3)

  tuple-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  pr1 (tuple-Euclidean-Domain-Semigroup n) =
    tuple-Set (set-Euclidean-Domain R) n
  pr1 (pr2 (tuple-Euclidean-Domain-Semigroup n)) = add-tuple-Euclidean-Domain
  pr2 (pr2 (tuple-Euclidean-Domain-Semigroup n)) =
    associative-add-tuple-Euclidean-Domain

  left-unit-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id (add-tuple-Euclidean-Domain (zero-tuple-Euclidean-Domain R) v) v
  left-unit-law-add-tuple-Euclidean-Domain empty-tuple = refl
  left-unit-law-add-tuple-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Euclidean-Domain R x)
      ( left-unit-law-add-tuple-Euclidean-Domain v)

  right-unit-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id (add-tuple-Euclidean-Domain v (zero-tuple-Euclidean-Domain R)) v
  right-unit-law-add-tuple-Euclidean-Domain empty-tuple = refl
  right-unit-law-add-tuple-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Euclidean-Domain R x)
      ( right-unit-law-add-tuple-Euclidean-Domain v)

  tuple-Euclidean-Domain-Monoid : ℕ → Monoid l
  pr1 (tuple-Euclidean-Domain-Monoid n) = tuple-Euclidean-Domain-Semigroup n
  pr1 (pr2 (tuple-Euclidean-Domain-Monoid n)) = zero-tuple-Euclidean-Domain R
  pr1 (pr2 (pr2 (tuple-Euclidean-Domain-Monoid n))) =
    left-unit-law-add-tuple-Euclidean-Domain
  pr2 (pr2 (pr2 (tuple-Euclidean-Domain-Monoid n))) =
    right-unit-law-add-tuple-Euclidean-Domain

  commutative-add-tuple-Euclidean-Domain :
    {n : ℕ} (v w : tuple-Euclidean-Domain R n) →
    Id (add-tuple-Euclidean-Domain v w) (add-tuple-Euclidean-Domain w v)
  commutative-add-tuple-Euclidean-Domain empty-tuple empty-tuple = refl
  commutative-add-tuple-Euclidean-Domain (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Euclidean-Domain R x y)
      ( commutative-add-tuple-Euclidean-Domain v w)

  tuple-Euclidean-Domain-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (tuple-Euclidean-Domain-Commutative-Monoid n) =
    tuple-Euclidean-Domain-Monoid n
  pr2 (tuple-Euclidean-Domain-Commutative-Monoid n) =
    commutative-add-tuple-Euclidean-Domain
```

#### Pointwise addition of functional tuples on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-functional-tuple-Euclidean-Domain :
    (n : ℕ) (v w : functional-tuple-Euclidean-Domain R n) →
    functional-tuple-Euclidean-Domain R n
  add-functional-tuple-Euclidean-Domain n =
    binary-map-functional-tuple n (add-Euclidean-Domain R)

  associative-add-functional-tuple-Euclidean-Domain :
    (n : ℕ) (v1 v2 v3 : functional-tuple-Euclidean-Domain R n) →
    ( add-functional-tuple-Euclidean-Domain
      ( n)
      ( add-functional-tuple-Euclidean-Domain n v1 v2)
      ( v3)) ＝
    ( add-functional-tuple-Euclidean-Domain
      ( n)
      ( v1)
      ( add-functional-tuple-Euclidean-Domain n v2 v3))
  associative-add-functional-tuple-Euclidean-Domain n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Euclidean-Domain R (v1 i) (v2 i) (v3 i))

  functional-tuple-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  pr1 (functional-tuple-Euclidean-Domain-Semigroup n) =
    functional-tuple-Set (set-Euclidean-Domain R) n
  pr1 (pr2 (functional-tuple-Euclidean-Domain-Semigroup n)) =
    add-functional-tuple-Euclidean-Domain n
  pr2 (pr2 (functional-tuple-Euclidean-Domain-Semigroup n)) =
    associative-add-functional-tuple-Euclidean-Domain n

  left-unit-law-add-functional-tuple-Euclidean-Domain :
    (n : ℕ) (v : functional-tuple-Euclidean-Domain R n) →
    ( add-functional-tuple-Euclidean-Domain
      ( n)
      ( zero-functional-tuple-Euclidean-Domain R n)
      ( v)) ＝
    ( v)
  left-unit-law-add-functional-tuple-Euclidean-Domain n v =
    eq-htpy (λ i → left-unit-law-add-Euclidean-Domain R (v i))

  right-unit-law-add-functional-tuple-Euclidean-Domain :
    (n : ℕ) (v : functional-tuple-Euclidean-Domain R n) →
    ( add-functional-tuple-Euclidean-Domain
      ( n)
      ( v)
      ( zero-functional-tuple-Euclidean-Domain R n)) ＝
    ( v)
  right-unit-law-add-functional-tuple-Euclidean-Domain n v =
    eq-htpy (λ i → right-unit-law-add-Euclidean-Domain R (v i))

  functional-tuple-Euclidean-Domain-Monoid : ℕ → Monoid l
  pr1 (functional-tuple-Euclidean-Domain-Monoid n) =
    functional-tuple-Euclidean-Domain-Semigroup n
  pr1 (pr2 (functional-tuple-Euclidean-Domain-Monoid n)) =
    zero-functional-tuple-Euclidean-Domain R n
  pr1 (pr2 (pr2 (functional-tuple-Euclidean-Domain-Monoid n))) =
    left-unit-law-add-functional-tuple-Euclidean-Domain n
  pr2 (pr2 (pr2 (functional-tuple-Euclidean-Domain-Monoid n))) =
    right-unit-law-add-functional-tuple-Euclidean-Domain n

  commutative-add-functional-tuple-Euclidean-Domain :
    (n : ℕ) (v w : functional-tuple-Euclidean-Domain R n) →
    add-functional-tuple-Euclidean-Domain n v w ＝
    add-functional-tuple-Euclidean-Domain n w v
  commutative-add-functional-tuple-Euclidean-Domain n v w =
    eq-htpy (λ i → commutative-add-Euclidean-Domain R (v i) (w i))

  functional-tuple-Euclidean-Domain-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  pr1 (functional-tuple-Euclidean-Domain-Commutative-Monoid n) =
    functional-tuple-Euclidean-Domain-Monoid n
  pr2 (functional-tuple-Euclidean-Domain-Commutative-Monoid n) =
    commutative-add-functional-tuple-Euclidean-Domain n
```

### The negative of a tuple on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  neg-tuple-Euclidean-Domain :
    {n : ℕ} → tuple-Euclidean-Domain R n → tuple-Euclidean-Domain R n
  neg-tuple-Euclidean-Domain = map-tuple (neg-Euclidean-Domain R)

  left-inverse-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id
      ( add-tuple-Euclidean-Domain R (neg-tuple-Euclidean-Domain v) v)
      ( zero-tuple-Euclidean-Domain R)
  left-inverse-law-add-tuple-Euclidean-Domain empty-tuple = refl
  left-inverse-law-add-tuple-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( left-inverse-law-add-Euclidean-Domain R x)
      ( left-inverse-law-add-tuple-Euclidean-Domain v)

  right-inverse-law-add-tuple-Euclidean-Domain :
    {n : ℕ} (v : tuple-Euclidean-Domain R n) →
    Id
      ( add-tuple-Euclidean-Domain R v (neg-tuple-Euclidean-Domain v))
      ( zero-tuple-Euclidean-Domain R)
  right-inverse-law-add-tuple-Euclidean-Domain empty-tuple = refl
  right-inverse-law-add-tuple-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( right-inverse-law-add-Euclidean-Domain R x)
      ( right-inverse-law-add-tuple-Euclidean-Domain v)

  is-unital-tuple-Euclidean-Domain :
    (n : ℕ) → is-unital (add-tuple-Euclidean-Domain R {n})
  pr1 (is-unital-tuple-Euclidean-Domain n) = zero-tuple-Euclidean-Domain R
  pr1 (pr2 (is-unital-tuple-Euclidean-Domain n)) =
    left-unit-law-add-tuple-Euclidean-Domain R
  pr2 (pr2 (is-unital-tuple-Euclidean-Domain n)) =
    right-unit-law-add-tuple-Euclidean-Domain R

  is-group-tuple-Euclidean-Domain :
    (n : ℕ) → is-group-Semigroup (tuple-Euclidean-Domain-Semigroup R n)
  pr1 (is-group-tuple-Euclidean-Domain n) = is-unital-tuple-Euclidean-Domain n
  pr1 (pr2 (is-group-tuple-Euclidean-Domain n)) = neg-tuple-Euclidean-Domain
  pr1 (pr2 (pr2 (is-group-tuple-Euclidean-Domain n))) =
    left-inverse-law-add-tuple-Euclidean-Domain
  pr2 (pr2 (pr2 (is-group-tuple-Euclidean-Domain n))) =
    right-inverse-law-add-tuple-Euclidean-Domain

  tuple-Euclidean-Domain-Group : ℕ → Group l
  pr1 (tuple-Euclidean-Domain-Group n) = tuple-Euclidean-Domain-Semigroup R n
  pr2 (tuple-Euclidean-Domain-Group n) = is-group-tuple-Euclidean-Domain n

  tuple-Euclidean-Domain-Ab : ℕ → Ab l
  pr1 (tuple-Euclidean-Domain-Ab n) = tuple-Euclidean-Domain-Group n
  pr2 (tuple-Euclidean-Domain-Ab n) = commutative-add-tuple-Euclidean-Domain R
```
