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
open import linear-algebra.functoriality-tuples
open import linear-algebra.tuples

open import ring-theory.semirings
```

</details>

## Idea

Given a ring `R`, the type `tuple n R` of `R`-tuples is an `R`-module

## Definitions

### Listed tuples on semirings

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

### Functional tuples on rings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  functional-tuple-Semiring : ℕ → UU l
  functional-tuple-Semiring = functional-tuple (type-Semiring R)

  head-functional-tuple-Semiring :
    (n : ℕ) → functional-tuple-Semiring (succ-ℕ n) → type-Semiring R
  head-functional-tuple-Semiring n v = head-functional-tuple n v

  tail-functional-tuple-Semiring :
    (n : ℕ) → functional-tuple-Semiring (succ-ℕ n) → functional-tuple-Semiring n
  tail-functional-tuple-Semiring = tail-functional-tuple

  cons-functional-tuple-Semiring :
    (n : ℕ) → type-Semiring R →
    functional-tuple-Semiring n → functional-tuple-Semiring (succ-ℕ n)
  cons-functional-tuple-Semiring = cons-functional-tuple

  snoc-functional-tuple-Semiring :
    (n : ℕ) → functional-tuple-Semiring n → type-Semiring R →
    functional-tuple-Semiring (succ-ℕ n)
  snoc-functional-tuple-Semiring = snoc-functional-tuple
```

### Zero tuple on a ring

#### The zero listed tuple

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-tuple-Semiring : {n : ℕ} → tuple-Semiring R n
  zero-tuple-Semiring = constant-tuple (zero-Semiring R)
```

#### The zero functional tuple

```agda
module _
  {l : Level} (R : Semiring l)
  where

  zero-functional-tuple-Semiring : (n : ℕ) → functional-tuple-Semiring R n
  zero-functional-tuple-Semiring n i = zero-Semiring R
```

### Pointwise addition of tuples on a ring

#### Pointwise addition of listed tuples on a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-tuple-Semiring :
    {n : ℕ} → tuple-Semiring R n → tuple-Semiring R n → tuple-Semiring R n
  add-tuple-Semiring = binary-map-tuple (add-Semiring R)

  associative-add-tuple-Semiring :
    {n : ℕ} (v1 v2 v3 : tuple-Semiring R n) →
    add-tuple-Semiring (add-tuple-Semiring v1 v2) v3 ＝
    add-tuple-Semiring v1 (add-tuple-Semiring v2 v3)
  associative-add-tuple-Semiring empty-tuple empty-tuple empty-tuple = refl
  associative-add-tuple-Semiring (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Semiring R x y z)
      ( associative-add-tuple-Semiring v1 v2 v3)

  tuple-Semiring-Semigroup : ℕ → Semigroup l
  pr1 (tuple-Semiring-Semigroup n) = tuple-Set (set-Semiring R) n
  pr1 (pr2 (tuple-Semiring-Semigroup n)) = add-tuple-Semiring
  pr2 (pr2 (tuple-Semiring-Semigroup n)) = associative-add-tuple-Semiring

  left-unit-law-add-tuple-Semiring :
    {n : ℕ} (v : tuple-Semiring R n) →
    add-tuple-Semiring (zero-tuple-Semiring R) v ＝ v
  left-unit-law-add-tuple-Semiring empty-tuple = refl
  left-unit-law-add-tuple-Semiring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Semiring R x)
      ( left-unit-law-add-tuple-Semiring v)

  right-unit-law-add-tuple-Semiring :
    {n : ℕ} (v : tuple-Semiring R n) →
    add-tuple-Semiring v (zero-tuple-Semiring R) ＝ v
  right-unit-law-add-tuple-Semiring empty-tuple = refl
  right-unit-law-add-tuple-Semiring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Semiring R x)
      ( right-unit-law-add-tuple-Semiring v)

  tuple-Semiring-Monoid : ℕ → Monoid l
  pr1 (tuple-Semiring-Monoid n) = tuple-Semiring-Semigroup n
  pr1 (pr2 (tuple-Semiring-Monoid n)) = zero-tuple-Semiring R
  pr1 (pr2 (pr2 (tuple-Semiring-Monoid n))) = left-unit-law-add-tuple-Semiring
  pr2 (pr2 (pr2 (tuple-Semiring-Monoid n))) = right-unit-law-add-tuple-Semiring

  commutative-add-tuple-Semiring :
    {n : ℕ} (v w : tuple-Semiring R n) →
    add-tuple-Semiring v w ＝ add-tuple-Semiring w v
  commutative-add-tuple-Semiring empty-tuple empty-tuple = refl
  commutative-add-tuple-Semiring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Semiring R x y)
      ( commutative-add-tuple-Semiring v w)

  tuple-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (tuple-Semiring-Commutative-Monoid n) = tuple-Semiring-Monoid n
  pr2 (tuple-Semiring-Commutative-Monoid n) = commutative-add-tuple-Semiring
```

#### Pointwise addition of functional tuples on a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-functional-tuple-Semiring :
    (n : ℕ) (v w : functional-tuple-Semiring R n) →
    functional-tuple-Semiring R n
  add-functional-tuple-Semiring n =
    binary-map-functional-tuple n (add-Semiring R)

  associative-add-functional-tuple-Semiring :
    (n : ℕ) (v1 v2 v3 : functional-tuple-Semiring R n) →
    ( add-functional-tuple-Semiring
      ( n)
      ( add-functional-tuple-Semiring n v1 v2)
      ( v3)) ＝
    ( add-functional-tuple-Semiring
      ( n)
      ( v1)
      ( add-functional-tuple-Semiring n v2 v3))
  associative-add-functional-tuple-Semiring n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Semiring R (v1 i) (v2 i) (v3 i))

  functional-tuple-Semiring-Semigroup : ℕ → Semigroup l
  pr1 (functional-tuple-Semiring-Semigroup n) =
    functional-tuple-Set (set-Semiring R) n
  pr1 (pr2 (functional-tuple-Semiring-Semigroup n)) =
    add-functional-tuple-Semiring n
  pr2 (pr2 (functional-tuple-Semiring-Semigroup n)) =
    associative-add-functional-tuple-Semiring n

  left-unit-law-add-functional-tuple-Semiring :
    (n : ℕ) (v : functional-tuple-Semiring R n) →
    add-functional-tuple-Semiring n (zero-functional-tuple-Semiring R n) v ＝ v
  left-unit-law-add-functional-tuple-Semiring n v =
    eq-htpy (λ i → left-unit-law-add-Semiring R (v i))

  right-unit-law-add-functional-tuple-Semiring :
    (n : ℕ) (v : functional-tuple-Semiring R n) →
    add-functional-tuple-Semiring n v (zero-functional-tuple-Semiring R n) ＝ v
  right-unit-law-add-functional-tuple-Semiring n v =
    eq-htpy (λ i → right-unit-law-add-Semiring R (v i))

  functional-tuple-Semiring-Monoid : ℕ → Monoid l
  pr1 (functional-tuple-Semiring-Monoid n) =
    functional-tuple-Semiring-Semigroup n
  pr1 (pr2 (functional-tuple-Semiring-Monoid n)) =
    zero-functional-tuple-Semiring R n
  pr1 (pr2 (pr2 (functional-tuple-Semiring-Monoid n))) =
    left-unit-law-add-functional-tuple-Semiring n
  pr2 (pr2 (pr2 (functional-tuple-Semiring-Monoid n))) =
    right-unit-law-add-functional-tuple-Semiring n

  commutative-add-functional-tuple-Semiring :
    (n : ℕ) (v w : functional-tuple-Semiring R n) →
    add-functional-tuple-Semiring n v w ＝ add-functional-tuple-Semiring n w v
  commutative-add-functional-tuple-Semiring n v w =
    eq-htpy (λ i → commutative-add-Semiring R (v i) (w i))

  functional-tuple-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (functional-tuple-Semiring-Commutative-Monoid n) =
    functional-tuple-Semiring-Monoid n
  pr2 (functional-tuple-Semiring-Commutative-Monoid n) =
    commutative-add-functional-tuple-Semiring n
```
