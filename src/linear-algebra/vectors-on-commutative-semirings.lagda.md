# Vectors on commutative semirings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module linear-algebra.vectors-on-commutative-semirings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings funext univalence truncations

open import elementary-number-theory.natural-numbers

open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.commutative-monoids funext univalence truncations
open import group-theory.monoids funext univalence truncations
open import group-theory.semigroups funext univalence

open import linear-algebra.constant-vectors funext univalence truncations
open import linear-algebra.vectors-on-semirings funext univalence truncations
```

</details>

## Idea

Vectors on a commutative semiring `R` are vectors on the underlying type of `R`.
The commutative semiring structure on `R` induces further structure on the type
of vectors on `R`.

## Definitions

### Listed vectors on commutative semirings

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  vec-Commutative-Semiring : ℕ → UU l
  vec-Commutative-Semiring =
    vec-Semiring (semiring-Commutative-Semiring R)

  head-vec-Commutative-Semiring :
    {n : ℕ} → vec-Commutative-Semiring (succ-ℕ n) → type-Commutative-Semiring R
  head-vec-Commutative-Semiring =
    head-vec-Semiring (semiring-Commutative-Semiring R)

  tail-vec-Commutative-Semiring :
    {n : ℕ} → vec-Commutative-Semiring (succ-ℕ n) → vec-Commutative-Semiring n
  tail-vec-Commutative-Semiring =
    tail-vec-Semiring (semiring-Commutative-Semiring R)

  snoc-vec-Commutative-Semiring :
    {n : ℕ} → vec-Commutative-Semiring n → type-Commutative-Semiring R →
    vec-Commutative-Semiring (succ-ℕ n)
  snoc-vec-Commutative-Semiring =
    snoc-vec-Semiring (semiring-Commutative-Semiring R)
```

### Functional vectors on commutative semirings

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  functional-vec-Commutative-Semiring : ℕ → UU l
  functional-vec-Commutative-Semiring =
    functional-vec-Semiring (semiring-Commutative-Semiring R)

  head-functional-vec-Commutative-Semiring :
    (n : ℕ) → functional-vec-Commutative-Semiring (succ-ℕ n) →
    type-Commutative-Semiring R
  head-functional-vec-Commutative-Semiring =
    head-functional-vec-Semiring (semiring-Commutative-Semiring R)

  tail-functional-vec-Commutative-Semiring :
    (n : ℕ) → functional-vec-Commutative-Semiring (succ-ℕ n) →
    functional-vec-Commutative-Semiring n
  tail-functional-vec-Commutative-Semiring =
    tail-functional-vec-Semiring (semiring-Commutative-Semiring R)

  cons-functional-vec-Commutative-Semiring :
    (n : ℕ) → type-Commutative-Semiring R →
    functional-vec-Commutative-Semiring n →
    functional-vec-Commutative-Semiring (succ-ℕ n)
  cons-functional-vec-Commutative-Semiring =
    cons-functional-vec-Semiring (semiring-Commutative-Semiring R)

  snoc-functional-vec-Commutative-Semiring :
    (n : ℕ) → functional-vec-Commutative-Semiring n →
    type-Commutative-Semiring R → functional-vec-Commutative-Semiring (succ-ℕ n)
  snoc-functional-vec-Commutative-Semiring =
    snoc-functional-vec-Semiring (semiring-Commutative-Semiring R)
```

### Zero vector on a commutative semiring

#### The zero listed vector

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-vec-Commutative-Semiring : {n : ℕ} → vec-Commutative-Semiring R n
  zero-vec-Commutative-Semiring = constant-vec (zero-Commutative-Semiring R)
```

#### The zero functional vector

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-functional-vec-Commutative-Semiring :
    (n : ℕ) → functional-vec-Commutative-Semiring R n
  zero-functional-vec-Commutative-Semiring n i = zero-Commutative-Semiring R
```

### Pointwise addition of vectors on a commutative semiring

#### Pointwise addition of listed vectors on a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  add-vec-Commutative-Semiring :
    {n : ℕ} → vec-Commutative-Semiring R n → vec-Commutative-Semiring R n →
    vec-Commutative-Semiring R n
  add-vec-Commutative-Semiring =
    add-vec-Semiring (semiring-Commutative-Semiring R)

  associative-add-vec-Commutative-Semiring :
    {n : ℕ} (v1 v2 v3 : vec-Commutative-Semiring R n) →
    add-vec-Commutative-Semiring (add-vec-Commutative-Semiring v1 v2) v3 ＝
    add-vec-Commutative-Semiring v1 (add-vec-Commutative-Semiring v2 v3)
  associative-add-vec-Commutative-Semiring =
    associative-add-vec-Semiring (semiring-Commutative-Semiring R)

  vec-Commutative-Semiring-Semigroup : ℕ → Semigroup l
  vec-Commutative-Semiring-Semigroup =
    vec-Semiring-Semigroup (semiring-Commutative-Semiring R)

  left-unit-law-add-vec-Commutative-Semiring :
    {n : ℕ} (v : vec-Commutative-Semiring R n) →
    add-vec-Commutative-Semiring (zero-vec-Commutative-Semiring R) v ＝ v
  left-unit-law-add-vec-Commutative-Semiring =
    left-unit-law-add-vec-Semiring (semiring-Commutative-Semiring R)

  right-unit-law-add-vec-Commutative-Semiring :
    {n : ℕ} (v : vec-Commutative-Semiring R n) →
    add-vec-Commutative-Semiring v (zero-vec-Commutative-Semiring R) ＝ v
  right-unit-law-add-vec-Commutative-Semiring =
    right-unit-law-add-vec-Semiring (semiring-Commutative-Semiring R)

  vec-Commutative-Semiring-Monoid : ℕ → Monoid l
  vec-Commutative-Semiring-Monoid =
    vec-Semiring-Monoid (semiring-Commutative-Semiring R)

  commutative-add-vec-Commutative-Semiring :
    {n : ℕ} (v w : vec-Commutative-Semiring R n) →
    add-vec-Commutative-Semiring v w ＝ add-vec-Commutative-Semiring w v
  commutative-add-vec-Commutative-Semiring =
    commutative-add-vec-Semiring (semiring-Commutative-Semiring R)

  vec-Commutative-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  vec-Commutative-Semiring-Commutative-Monoid =
    vec-Semiring-Commutative-Monoid (semiring-Commutative-Semiring R)
```

#### Pointwise addition of functional vectors on a commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  add-functional-vec-Commutative-Semiring :
    (n : ℕ) (v w : functional-vec-Commutative-Semiring R n) →
    functional-vec-Commutative-Semiring R n
  add-functional-vec-Commutative-Semiring =
    add-functional-vec-Semiring (semiring-Commutative-Semiring R)

  associative-add-functional-vec-Commutative-Semiring :
    (n : ℕ) (v1 v2 v3 : functional-vec-Commutative-Semiring R n) →
    ( add-functional-vec-Commutative-Semiring n
      ( add-functional-vec-Commutative-Semiring n v1 v2) v3) ＝
    ( add-functional-vec-Commutative-Semiring n v1
      ( add-functional-vec-Commutative-Semiring n v2 v3))
  associative-add-functional-vec-Commutative-Semiring =
    associative-add-functional-vec-Semiring (semiring-Commutative-Semiring R)

  functional-vec-Commutative-Semiring-Semigroup : ℕ → Semigroup l
  functional-vec-Commutative-Semiring-Semigroup =
    functional-vec-Semiring-Semigroup (semiring-Commutative-Semiring R)

  left-unit-law-add-functional-vec-Commutative-Semiring :
    (n : ℕ) (v : functional-vec-Commutative-Semiring R n) →
    add-functional-vec-Commutative-Semiring n
      ( zero-functional-vec-Commutative-Semiring R n) v ＝ v
  left-unit-law-add-functional-vec-Commutative-Semiring =
    left-unit-law-add-functional-vec-Semiring (semiring-Commutative-Semiring R)

  right-unit-law-add-functional-vec-Commutative-Semiring :
    (n : ℕ) (v : functional-vec-Commutative-Semiring R n) →
    add-functional-vec-Commutative-Semiring n v
      ( zero-functional-vec-Commutative-Semiring R n) ＝ v
  right-unit-law-add-functional-vec-Commutative-Semiring =
    right-unit-law-add-functional-vec-Semiring (semiring-Commutative-Semiring R)

  functional-vec-Commutative-Semiring-Monoid : ℕ → Monoid l
  functional-vec-Commutative-Semiring-Monoid =
    functional-vec-Semiring-Monoid (semiring-Commutative-Semiring R)

  commutative-add-functional-vec-Commutative-Semiring :
    (n : ℕ) (v w : functional-vec-Commutative-Semiring R n) →
    add-functional-vec-Commutative-Semiring n v w ＝
    add-functional-vec-Commutative-Semiring n w v
  commutative-add-functional-vec-Commutative-Semiring =
    commutative-add-functional-vec-Semiring (semiring-Commutative-Semiring R)

  functional-vec-Commutative-Semiring-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  functional-vec-Commutative-Semiring-Commutative-Monoid =
    functional-vec-Semiring-Commutative-Monoid (semiring-Commutative-Semiring R)
```
