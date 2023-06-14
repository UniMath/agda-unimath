# Vectors on rings

```agda
module linear-algebra.vectors-on-rings where
```

<details><summary>Imports</summary>

```agda
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

open import linear-algebra.constant-vectors
open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors

open import ring-theory.rings
```

</details>

## Idea

Given a ring `R`, the type `vec n R` of `R`-vectors is an `R`-module.

## Definitions

### Listed vectors on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  vec-Ring : ℕ → UU l
  vec-Ring = vec (type-Ring R)

  head-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → type-Ring R
  head-vec-Ring v = head-vec v

  tail-vec-Ring : {n : ℕ} → vec-Ring (succ-ℕ n) → vec-Ring n
  tail-vec-Ring v = tail-vec v

  snoc-vec-Ring : {n : ℕ} → vec-Ring n → type-Ring R → vec-Ring (succ-ℕ n)
  snoc-vec-Ring v r = snoc-vec v r
```

### Functional vectors on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  functional-vec-Ring : ℕ → UU l
  functional-vec-Ring = functional-vec (type-Ring R)

  head-functional-vec-Ring :
    (n : ℕ) → functional-vec-Ring (succ-ℕ n) → type-Ring R
  head-functional-vec-Ring n v = head-functional-vec n v

  tail-functional-vec-Ring :
    (n : ℕ) → functional-vec-Ring (succ-ℕ n) → functional-vec-Ring n
  tail-functional-vec-Ring = tail-functional-vec

  cons-functional-vec-Ring :
    (n : ℕ) → type-Ring R →
    functional-vec-Ring n → functional-vec-Ring (succ-ℕ n)
  cons-functional-vec-Ring = cons-functional-vec

  snoc-functional-vec-Ring :
    (n : ℕ) → functional-vec-Ring n → type-Ring R →
    functional-vec-Ring (succ-ℕ n)
  snoc-functional-vec-Ring = snoc-functional-vec
```

### Zero vector on a ring

#### The zero listed vector

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-vec-Ring : {n : ℕ} → vec-Ring R n
  zero-vec-Ring = constant-vec (zero-Ring R)
```

#### The zero functional vector

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-functional-vec-Ring : (n : ℕ) → functional-vec-Ring R n
  zero-functional-vec-Ring n i = zero-Ring R
```

### Pointwise addition of vectors on a ring

#### Pointwise addition of listed vectors on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-vec-Ring : {n : ℕ} → vec-Ring R n → vec-Ring R n → vec-Ring R n
  add-vec-Ring = binary-map-vec (add-Ring R)

  associative-add-vec-Ring :
    {n : ℕ} (v1 v2 v3 : vec-Ring R n) →
    Id
      ( add-vec-Ring (add-vec-Ring v1 v2) v3)
      ( add-vec-Ring v1 (add-vec-Ring v2 v3))
  associative-add-vec-Ring empty-vec empty-vec empty-vec = refl
  associative-add-vec-Ring (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Ring R x y z)
      ( associative-add-vec-Ring v1 v2 v3)

  vec-Ring-Semigroup : ℕ → Semigroup l
  pr1 (vec-Ring-Semigroup n) = vec-Set (set-Ring R) n
  pr1 (pr2 (vec-Ring-Semigroup n)) = add-vec-Ring
  pr2 (pr2 (vec-Ring-Semigroup n)) = associative-add-vec-Ring

  left-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring (zero-vec-Ring R) v) v
  left-unit-law-add-vec-Ring empty-vec = refl
  left-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Ring R x)
      ( left-unit-law-add-vec-Ring v)

  right-unit-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) → Id (add-vec-Ring v (zero-vec-Ring R)) v
  right-unit-law-add-vec-Ring empty-vec = refl
  right-unit-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Ring R x)
      ( right-unit-law-add-vec-Ring v)

  vec-Ring-Monoid : ℕ → Monoid l
  pr1 (vec-Ring-Monoid n) = vec-Ring-Semigroup n
  pr1 (pr2 (vec-Ring-Monoid n)) = zero-vec-Ring R
  pr1 (pr2 (pr2 (vec-Ring-Monoid n))) = left-unit-law-add-vec-Ring
  pr2 (pr2 (pr2 (vec-Ring-Monoid n))) = right-unit-law-add-vec-Ring

  commutative-add-vec-Ring :
    {n : ℕ} (v w : vec-Ring R n) → Id (add-vec-Ring v w) (add-vec-Ring w v)
  commutative-add-vec-Ring empty-vec empty-vec = refl
  commutative-add-vec-Ring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Ring R x y)
      ( commutative-add-vec-Ring v w)

  vec-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (vec-Ring-Commutative-Monoid n) = vec-Ring-Monoid n
  pr2 (vec-Ring-Commutative-Monoid n) = commutative-add-vec-Ring
```

#### Pointwise addition of functional vectors on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-functional-vec-Ring :
    (n : ℕ) (v w : functional-vec-Ring R n) → functional-vec-Ring R n
  add-functional-vec-Ring n = binary-map-functional-vec n (add-Ring R)

  associative-add-functional-vec-Ring :
    (n : ℕ) (v1 v2 v3 : functional-vec-Ring R n) →
    ( add-functional-vec-Ring n (add-functional-vec-Ring n v1 v2) v3) ＝
    ( add-functional-vec-Ring n v1 (add-functional-vec-Ring n v2 v3))
  associative-add-functional-vec-Ring n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Ring R (v1 i) (v2 i) (v3 i))

  functional-vec-Ring-Semigroup : ℕ → Semigroup l
  pr1 (functional-vec-Ring-Semigroup n) = functional-vec-Set (set-Ring R) n
  pr1 (pr2 (functional-vec-Ring-Semigroup n)) = add-functional-vec-Ring n
  pr2 (pr2 (functional-vec-Ring-Semigroup n)) =
    associative-add-functional-vec-Ring n

  left-unit-law-add-functional-vec-Ring :
    (n : ℕ) (v : functional-vec-Ring R n) →
    add-functional-vec-Ring n (zero-functional-vec-Ring R n) v ＝ v
  left-unit-law-add-functional-vec-Ring n v =
    eq-htpy (λ i → left-unit-law-add-Ring R (v i))

  right-unit-law-add-functional-vec-Ring :
    (n : ℕ) (v : functional-vec-Ring R n) →
    add-functional-vec-Ring n v (zero-functional-vec-Ring R n) ＝ v
  right-unit-law-add-functional-vec-Ring n v =
    eq-htpy (λ i → right-unit-law-add-Ring R (v i))

  functional-vec-Ring-Monoid : ℕ → Monoid l
  pr1 (functional-vec-Ring-Monoid n) =
    functional-vec-Ring-Semigroup n
  pr1 (pr2 (functional-vec-Ring-Monoid n)) =
    zero-functional-vec-Ring R n
  pr1 (pr2 (pr2 (functional-vec-Ring-Monoid n))) =
    left-unit-law-add-functional-vec-Ring n
  pr2 (pr2 (pr2 (functional-vec-Ring-Monoid n))) =
    right-unit-law-add-functional-vec-Ring n

  commutative-add-functional-vec-Ring :
    (n : ℕ) (v w : functional-vec-Ring R n) →
    add-functional-vec-Ring n v w ＝ add-functional-vec-Ring n w v
  commutative-add-functional-vec-Ring n v w =
    eq-htpy (λ i → commutative-add-Ring R (v i) (w i))

  functional-vec-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (functional-vec-Ring-Commutative-Monoid n) =
    functional-vec-Ring-Monoid n
  pr2 (functional-vec-Ring-Commutative-Monoid n) =
    commutative-add-functional-vec-Ring n
```

### The negative of a vector on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-vec-Ring : {n : ℕ} → vec-Ring R n → vec-Ring R n
  neg-vec-Ring = map-vec (neg-Ring R)

  left-inverse-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) →
    Id (add-vec-Ring R (neg-vec-Ring v) v) (zero-vec-Ring R)
  left-inverse-law-add-vec-Ring empty-vec = refl
  left-inverse-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-inverse-law-add-Ring R x)
      ( left-inverse-law-add-vec-Ring v)

  right-inverse-law-add-vec-Ring :
    {n : ℕ} (v : vec-Ring R n) →
    Id (add-vec-Ring R v (neg-vec-Ring v)) (zero-vec-Ring R)
  right-inverse-law-add-vec-Ring empty-vec = refl
  right-inverse-law-add-vec-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-inverse-law-add-Ring R x)
      ( right-inverse-law-add-vec-Ring v)

  is-unital-vec-Ring : (n : ℕ) → is-unital (add-vec-Ring R {n})
  pr1 (is-unital-vec-Ring n) = zero-vec-Ring R
  pr1 (pr2 (is-unital-vec-Ring n)) = left-unit-law-add-vec-Ring R
  pr2 (pr2 (is-unital-vec-Ring n)) = right-unit-law-add-vec-Ring R

  is-group-vec-Ring : (n : ℕ) → is-group (vec-Ring-Semigroup R n)
  pr1 (is-group-vec-Ring n) = is-unital-vec-Ring n
  pr1 (pr2 (is-group-vec-Ring n)) = neg-vec-Ring
  pr1 (pr2 (pr2 (is-group-vec-Ring n))) = left-inverse-law-add-vec-Ring
  pr2 (pr2 (pr2 (is-group-vec-Ring n))) = right-inverse-law-add-vec-Ring

  vec-Ring-Group : ℕ → Group l
  pr1 (vec-Ring-Group n) = vec-Ring-Semigroup R n
  pr2 (vec-Ring-Group n) = is-group-vec-Ring n

  vec-Ring-Ab : ℕ → Ab l
  pr1 (vec-Ring-Ab n) = vec-Ring-Group n
  pr2 (vec-Ring-Ab n) = commutative-add-vec-Ring R
```
