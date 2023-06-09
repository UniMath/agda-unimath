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
  vec-Semiring = vec (type-Semiring R)

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
  functional-vec-Semiring = functional-vec (type-Semiring R)

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
  zero-vec-Semiring = constant-vec (zero-Semiring R)
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
  add-vec-Semiring = binary-map-vec (add-Semiring R)

  associative-add-vec-Semiring :
    {n : ℕ} (v1 v2 v3 : vec-Semiring R n) →
    add-vec-Semiring (add-vec-Semiring v1 v2) v3 ＝
    add-vec-Semiring v1 (add-vec-Semiring v2 v3)
  associative-add-vec-Semiring empty-vec empty-vec empty-vec = refl
  associative-add-vec-Semiring (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Semiring R x y z)
      ( associative-add-vec-Semiring v1 v2 v3)

  vec-Semiring-Semigroup : ℕ → Semigroup l
  pr1 (vec-Semiring-Semigroup n) = vec-Set (set-Semiring R) n
  pr1 (pr2 (vec-Semiring-Semigroup n)) = add-vec-Semiring
  pr2 (pr2 (vec-Semiring-Semigroup n)) = associative-add-vec-Semiring

  left-unit-law-add-vec-Semiring :
    {n : ℕ} (v : vec-Semiring R n) →
    add-vec-Semiring (zero-vec-Semiring R) v ＝ v
  left-unit-law-add-vec-Semiring empty-vec = refl
  left-unit-law-add-vec-Semiring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Semiring R x)
      ( left-unit-law-add-vec-Semiring v)

  right-unit-law-add-vec-Semiring :
    {n : ℕ} (v : vec-Semiring R n) →
    add-vec-Semiring v (zero-vec-Semiring R) ＝ v
  right-unit-law-add-vec-Semiring empty-vec = refl
  right-unit-law-add-vec-Semiring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Semiring R x)
      ( right-unit-law-add-vec-Semiring v)

  vec-Semiring-Monoid : ℕ → Monoid l
  pr1 (vec-Semiring-Monoid n) = vec-Semiring-Semigroup n
  pr1 (pr2 (vec-Semiring-Monoid n)) = zero-vec-Semiring R
  pr1 (pr2 (pr2 (vec-Semiring-Monoid n))) = left-unit-law-add-vec-Semiring
  pr2 (pr2 (pr2 (vec-Semiring-Monoid n))) = right-unit-law-add-vec-Semiring

  commutative-add-vec-Semiring :
    {n : ℕ} (v w : vec-Semiring R n) →
    add-vec-Semiring v w ＝ add-vec-Semiring w v
  commutative-add-vec-Semiring empty-vec empty-vec = refl
  commutative-add-vec-Semiring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Semiring R x y)
      ( commutative-add-vec-Semiring v w)

  vec-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (vec-Semiring-Commutative-Monoid n) = vec-Semiring-Monoid n
  pr2 (vec-Semiring-Commutative-Monoid n) = commutative-add-vec-Semiring
```

#### Pointwise addition of functional vectors on a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  add-functional-vec-Semiring :
    (n : ℕ) (v w : functional-vec-Semiring R n) → functional-vec-Semiring R n
  add-functional-vec-Semiring n = binary-map-functional-vec n (add-Semiring R)

  associative-add-functional-vec-Semiring :
    (n : ℕ) (v1 v2 v3 : functional-vec-Semiring R n) →
    ( add-functional-vec-Semiring n (add-functional-vec-Semiring n v1 v2) v3) ＝
    ( add-functional-vec-Semiring n v1 (add-functional-vec-Semiring n v2 v3))
  associative-add-functional-vec-Semiring n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Semiring R (v1 i) (v2 i) (v3 i))

  functional-vec-Semiring-Semigroup : ℕ → Semigroup l
  pr1 (functional-vec-Semiring-Semigroup n) =
    functional-vec-Set (set-Semiring R) n
  pr1 (pr2 (functional-vec-Semiring-Semigroup n)) =
    add-functional-vec-Semiring n
  pr2 (pr2 (functional-vec-Semiring-Semigroup n)) =
    associative-add-functional-vec-Semiring n

  left-unit-law-add-functional-vec-Semiring :
    (n : ℕ) (v : functional-vec-Semiring R n) →
    add-functional-vec-Semiring n (zero-functional-vec-Semiring R n) v ＝ v
  left-unit-law-add-functional-vec-Semiring n v =
    eq-htpy (λ i → left-unit-law-add-Semiring R (v i))

  right-unit-law-add-functional-vec-Semiring :
    (n : ℕ) (v : functional-vec-Semiring R n) →
    add-functional-vec-Semiring n v (zero-functional-vec-Semiring R n) ＝ v
  right-unit-law-add-functional-vec-Semiring n v =
    eq-htpy (λ i → right-unit-law-add-Semiring R (v i))

  functional-vec-Semiring-Monoid : ℕ → Monoid l
  pr1 (functional-vec-Semiring-Monoid n) =
    functional-vec-Semiring-Semigroup n
  pr1 (pr2 (functional-vec-Semiring-Monoid n)) =
    zero-functional-vec-Semiring R n
  pr1 (pr2 (pr2 (functional-vec-Semiring-Monoid n))) =
    left-unit-law-add-functional-vec-Semiring n
  pr2 (pr2 (pr2 (functional-vec-Semiring-Monoid n))) =
    right-unit-law-add-functional-vec-Semiring n

  commutative-add-functional-vec-Semiring :
    (n : ℕ) (v w : functional-vec-Semiring R n) →
    add-functional-vec-Semiring n v w ＝ add-functional-vec-Semiring n w v
  commutative-add-functional-vec-Semiring n v w =
    eq-htpy (λ i → commutative-add-Semiring R (v i) (w i))

  functional-vec-Semiring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (functional-vec-Semiring-Commutative-Monoid n) =
    functional-vec-Semiring-Monoid n
  pr2 (functional-vec-Semiring-Commutative-Monoid n) =
    commutative-add-functional-vec-Semiring n
```
