# Vectors on semirings

```agda
module linear-algebra.vectors-on-semirings where
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

open import linear-algebra.constant-vectors
open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors
open import linear-algebra.vectors-on-commutative-monoids

open import ring-theory.semirings
```

</details>

## Idea

Given a ring `R`, the type `vec n R` of `R`-vectors is an `R`-module

## Definitions

### Listed vectors on semirings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  vec-Semiring : ℕ → UU l
  vec-Semiring = vec-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  head-vec-Semiring : {n : ℕ} → vec-Semiring (succ-ℕ n) → type-Semiring R
  head-vec-Semiring v = head-vec v

  tail-vec-Semiring : {n : ℕ} → vec-Semiring (succ-ℕ n) → vec-Semiring n
  tail-vec-Semiring v = tail-vec v

  snoc-vec-Semiring :
    {n : ℕ} → vec-Semiring n → type-Semiring R → vec-Semiring (succ-ℕ n)
  snoc-vec-Semiring v r = snoc-vec v r
```

### Functional vectors on rings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  functional-vec-Semiring : ℕ → UU l
  functional-vec-Semiring =
    functional-vec-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  head-functional-vec-Semiring :
    (n : ℕ) → functional-vec-Semiring (succ-ℕ n) → type-Semiring R
  head-functional-vec-Semiring n v = head-functional-vec n v

  tail-functional-vec-Semiring :
    (n : ℕ) → functional-vec-Semiring (succ-ℕ n) → functional-vec-Semiring n
  tail-functional-vec-Semiring = tail-functional-vec

  cons-functional-vec-Semiring :
    (n : ℕ) → type-Semiring R →
    functional-vec-Semiring n → functional-vec-Semiring (succ-ℕ n)
  cons-functional-vec-Semiring = cons-functional-vec

  snoc-functional-vec-Semiring :
    (n : ℕ) → functional-vec-Semiring n → type-Semiring R →
    functional-vec-Semiring (succ-ℕ n)
  snoc-functional-vec-Semiring = snoc-functional-vec
```

### Zero vector on a ring

#### The zero listed vector

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-vec-Semiring : {n : ℕ} → vec-Semiring R n
  zero-vec-Semiring =
    one-vec-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

#### The zero functional vector

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-functional-vec-Semiring : (n : ℕ) → functional-vec-Semiring R n
  zero-functional-vec-Semiring n i = zero-Semiring R
```

### Pointwise addition of vectors on a ring

#### Pointwise addition of listed vectors on a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-vec-Semiring :
    {n : ℕ} → vec-Semiring R n → vec-Semiring R n → vec-Semiring R n
  add-vec-Semiring =
    mul-vec-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  associative-add-vec-Semiring :
    {n : ℕ} (v1 v2 v3 : vec-Semiring R n) →
    add-vec-Semiring (add-vec-Semiring v1 v2) v3 ＝
    add-vec-Semiring v1 (add-vec-Semiring v2 v3)
  associative-add-vec-Semiring =
    associative-mul-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  vec-Semiring-Semigroup : ℕ → Semigroup l
  vec-Semiring-Semigroup =
    vec-Commutative-Monoid-Semigroup (additive-commutative-monoid-Semiring R)

  left-unit-law-add-vec-Semiring :
    {n : ℕ} (v : vec-Semiring R n) →
    add-vec-Semiring (zero-vec-Semiring R) v ＝ v
  left-unit-law-add-vec-Semiring =
    left-unit-law-mul-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  right-unit-law-add-vec-Semiring :
    {n : ℕ} (v : vec-Semiring R n) →
    add-vec-Semiring v (zero-vec-Semiring R) ＝ v
  right-unit-law-add-vec-Semiring =
    right-unit-law-mul-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  vec-Semiring-Monoid : ℕ → Monoid l
  vec-Semiring-Monoid =
    vec-Commutative-Monoid-Monoid
      ( additive-commutative-monoid-Semiring R)

  commutative-add-vec-Semiring :
    {n : ℕ} (v w : vec-Semiring R n) →
    add-vec-Semiring v w ＝ add-vec-Semiring w v
  commutative-add-vec-Semiring =
    commutative-mul-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  vec-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  vec-Semiring-Commutative-Monoid =
    vec-Commutative-Monoid-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

#### Pointwise addition of functional vectors on a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-functional-vec-Semiring :
    (n : ℕ) (v w : functional-vec-Semiring R n) → functional-vec-Semiring R n
  add-functional-vec-Semiring =
    mul-functional-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  associative-add-functional-vec-Semiring :
    (n : ℕ) (v1 v2 v3 : functional-vec-Semiring R n) →
    ( add-functional-vec-Semiring n (add-functional-vec-Semiring n v1 v2) v3) ＝
    ( add-functional-vec-Semiring n v1 (add-functional-vec-Semiring n v2 v3))
  associative-add-functional-vec-Semiring =
    associative-mul-functional-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  functional-vec-Semiring-Semigroup : ℕ → Semigroup l
  functional-vec-Semiring-Semigroup =
    functional-vec-Commutative-Monoid-Semigroup
      ( additive-commutative-monoid-Semiring R)

  left-unit-law-add-functional-vec-Semiring :
    (n : ℕ) (v : functional-vec-Semiring R n) →
    add-functional-vec-Semiring n (zero-functional-vec-Semiring R n) v ＝ v
  left-unit-law-add-functional-vec-Semiring =
    left-unit-law-mul-functional-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  right-unit-law-add-functional-vec-Semiring :
    (n : ℕ) (v : functional-vec-Semiring R n) →
    add-functional-vec-Semiring n v (zero-functional-vec-Semiring R n) ＝ v
  right-unit-law-add-functional-vec-Semiring =
    right-unit-law-mul-functional-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  functional-vec-Semiring-Monoid : ℕ → Monoid l
  functional-vec-Semiring-Monoid =
    functional-vec-Commutative-Monoid-Monoid
      ( additive-commutative-monoid-Semiring R)

  commutative-add-functional-vec-Semiring :
    (n : ℕ) (v w : functional-vec-Semiring R n) →
    add-functional-vec-Semiring n v w ＝ add-functional-vec-Semiring n w v
  commutative-add-functional-vec-Semiring =
    commutative-mul-functional-vec-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  functional-vec-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  functional-vec-Semiring-Commutative-Monoid =
    functional-vec-Commutative-Monoid-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```
