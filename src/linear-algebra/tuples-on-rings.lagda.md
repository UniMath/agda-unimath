# Tuples on rings

```agda
module linear-algebra.tuples-on-rings where
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

open import linear-algebra.constant-tuples
open import linear-algebra.functoriality-tuples
open import linear-algebra.tuples

open import ring-theory.rings
```

</details>

## Idea

Given a [ring](ring-theory.rings.md) `R`, the type `tuple n R` of
`R`-[tuples](linear-algebra.tuples.md) is an
[Abelian group](group-theory.abelian-groups.md).

## Definitions

### Listed tuples on rings

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

### Functional tuples on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  functional-tuple-Ring : ℕ → UU l
  functional-tuple-Ring = functional-tuple (type-Ring R)

  head-functional-tuple-Ring :
    (n : ℕ) → functional-tuple-Ring (succ-ℕ n) → type-Ring R
  head-functional-tuple-Ring n v = head-functional-tuple n v

  tail-functional-tuple-Ring :
    (n : ℕ) → functional-tuple-Ring (succ-ℕ n) → functional-tuple-Ring n
  tail-functional-tuple-Ring = tail-functional-tuple

  cons-functional-tuple-Ring :
    (n : ℕ) → type-Ring R →
    functional-tuple-Ring n → functional-tuple-Ring (succ-ℕ n)
  cons-functional-tuple-Ring = cons-functional-tuple

  snoc-functional-tuple-Ring :
    (n : ℕ) → functional-tuple-Ring n → type-Ring R →
    functional-tuple-Ring (succ-ℕ n)
  snoc-functional-tuple-Ring = snoc-functional-tuple
```

### Zero tuple on a ring

#### The zero listed tuple

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-tuple-Ring : {n : ℕ} → tuple-Ring R n
  zero-tuple-Ring = constant-tuple (zero-Ring R)
```

#### The zero functional tuple

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-functional-tuple-Ring : (n : ℕ) → functional-tuple-Ring R n
  zero-functional-tuple-Ring n i = zero-Ring R
```

### Pointwise addition of tuples on a ring

#### Pointwise addition of listed tuples on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-tuple-Ring : {n : ℕ} → tuple-Ring R n → tuple-Ring R n → tuple-Ring R n
  add-tuple-Ring = binary-map-tuple (add-Ring R)

  associative-add-tuple-Ring :
    {n : ℕ} (v1 v2 v3 : tuple-Ring R n) →
    Id
      ( add-tuple-Ring (add-tuple-Ring v1 v2) v3)
      ( add-tuple-Ring v1 (add-tuple-Ring v2 v3))
  associative-add-tuple-Ring empty-tuple empty-tuple empty-tuple = refl
  associative-add-tuple-Ring (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Ring R x y z)
      ( associative-add-tuple-Ring v1 v2 v3)

  tuple-Ring-Semigroup : ℕ → Semigroup l
  pr1 (tuple-Ring-Semigroup n) = tuple-Set (set-Ring R) n
  pr1 (pr2 (tuple-Ring-Semigroup n)) = add-tuple-Ring
  pr2 (pr2 (tuple-Ring-Semigroup n)) = associative-add-tuple-Ring

  left-unit-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) → Id (add-tuple-Ring (zero-tuple-Ring R) v) v
  left-unit-law-add-tuple-Ring empty-tuple = refl
  left-unit-law-add-tuple-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Ring R x)
      ( left-unit-law-add-tuple-Ring v)

  right-unit-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) → Id (add-tuple-Ring v (zero-tuple-Ring R)) v
  right-unit-law-add-tuple-Ring empty-tuple = refl
  right-unit-law-add-tuple-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Ring R x)
      ( right-unit-law-add-tuple-Ring v)

  tuple-Ring-Monoid : ℕ → Monoid l
  pr1 (tuple-Ring-Monoid n) = tuple-Ring-Semigroup n
  pr1 (pr2 (tuple-Ring-Monoid n)) = zero-tuple-Ring R
  pr1 (pr2 (pr2 (tuple-Ring-Monoid n))) = left-unit-law-add-tuple-Ring
  pr2 (pr2 (pr2 (tuple-Ring-Monoid n))) = right-unit-law-add-tuple-Ring

  commutative-add-tuple-Ring :
    {n : ℕ} (v w : tuple-Ring R n) →
    Id (add-tuple-Ring v w) (add-tuple-Ring w v)
  commutative-add-tuple-Ring empty-tuple empty-tuple = refl
  commutative-add-tuple-Ring (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Ring R x y)
      ( commutative-add-tuple-Ring v w)

  tuple-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (tuple-Ring-Commutative-Monoid n) = tuple-Ring-Monoid n
  pr2 (tuple-Ring-Commutative-Monoid n) = commutative-add-tuple-Ring
```

#### Pointwise addition of functional tuples on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-functional-tuple-Ring :
    (n : ℕ) (v w : functional-tuple-Ring R n) → functional-tuple-Ring R n
  add-functional-tuple-Ring n = binary-map-functional-tuple n (add-Ring R)

  associative-add-functional-tuple-Ring :
    (n : ℕ) (v1 v2 v3 : functional-tuple-Ring R n) →
    ( add-functional-tuple-Ring n (add-functional-tuple-Ring n v1 v2) v3) ＝
    ( add-functional-tuple-Ring n v1 (add-functional-tuple-Ring n v2 v3))
  associative-add-functional-tuple-Ring n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Ring R (v1 i) (v2 i) (v3 i))

  functional-tuple-Ring-Semigroup : ℕ → Semigroup l
  pr1 (functional-tuple-Ring-Semigroup n) = functional-tuple-Set (set-Ring R) n
  pr1 (pr2 (functional-tuple-Ring-Semigroup n)) = add-functional-tuple-Ring n
  pr2 (pr2 (functional-tuple-Ring-Semigroup n)) =
    associative-add-functional-tuple-Ring n

  left-unit-law-add-functional-tuple-Ring :
    (n : ℕ) (v : functional-tuple-Ring R n) →
    add-functional-tuple-Ring n (zero-functional-tuple-Ring R n) v ＝ v
  left-unit-law-add-functional-tuple-Ring n v =
    eq-htpy (λ i → left-unit-law-add-Ring R (v i))

  right-unit-law-add-functional-tuple-Ring :
    (n : ℕ) (v : functional-tuple-Ring R n) →
    add-functional-tuple-Ring n v (zero-functional-tuple-Ring R n) ＝ v
  right-unit-law-add-functional-tuple-Ring n v =
    eq-htpy (λ i → right-unit-law-add-Ring R (v i))

  functional-tuple-Ring-Monoid : ℕ → Monoid l
  pr1 (functional-tuple-Ring-Monoid n) =
    functional-tuple-Ring-Semigroup n
  pr1 (pr2 (functional-tuple-Ring-Monoid n)) =
    zero-functional-tuple-Ring R n
  pr1 (pr2 (pr2 (functional-tuple-Ring-Monoid n))) =
    left-unit-law-add-functional-tuple-Ring n
  pr2 (pr2 (pr2 (functional-tuple-Ring-Monoid n))) =
    right-unit-law-add-functional-tuple-Ring n

  commutative-add-functional-tuple-Ring :
    (n : ℕ) (v w : functional-tuple-Ring R n) →
    add-functional-tuple-Ring n v w ＝ add-functional-tuple-Ring n w v
  commutative-add-functional-tuple-Ring n v w =
    eq-htpy (λ i → commutative-add-Ring R (v i) (w i))

  functional-tuple-Ring-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (functional-tuple-Ring-Commutative-Monoid n) =
    functional-tuple-Ring-Monoid n
  pr2 (functional-tuple-Ring-Commutative-Monoid n) =
    commutative-add-functional-tuple-Ring n
```

### The negative of a tuple on a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-tuple-Ring : {n : ℕ} → tuple-Ring R n → tuple-Ring R n
  neg-tuple-Ring = map-tuple (neg-Ring R)

  left-inverse-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) →
    Id (add-tuple-Ring R (neg-tuple-Ring v) v) (zero-tuple-Ring R)
  left-inverse-law-add-tuple-Ring empty-tuple = refl
  left-inverse-law-add-tuple-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-inverse-law-add-Ring R x)
      ( left-inverse-law-add-tuple-Ring v)

  right-inverse-law-add-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) →
    Id (add-tuple-Ring R v (neg-tuple-Ring v)) (zero-tuple-Ring R)
  right-inverse-law-add-tuple-Ring empty-tuple = refl
  right-inverse-law-add-tuple-Ring (x ∷ v) =
    ap-binary _∷_
      ( right-inverse-law-add-Ring R x)
      ( right-inverse-law-add-tuple-Ring v)

  is-unital-tuple-Ring : (n : ℕ) → is-unital (add-tuple-Ring R {n})
  pr1 (is-unital-tuple-Ring n) = zero-tuple-Ring R
  pr1 (pr2 (is-unital-tuple-Ring n)) = left-unit-law-add-tuple-Ring R
  pr2 (pr2 (is-unital-tuple-Ring n)) = right-unit-law-add-tuple-Ring R

  is-group-tuple-Ring : (n : ℕ) → is-group-Semigroup (tuple-Ring-Semigroup R n)
  pr1 (is-group-tuple-Ring n) = is-unital-tuple-Ring n
  pr1 (pr2 (is-group-tuple-Ring n)) = neg-tuple-Ring
  pr1 (pr2 (pr2 (is-group-tuple-Ring n))) = left-inverse-law-add-tuple-Ring
  pr2 (pr2 (pr2 (is-group-tuple-Ring n))) = right-inverse-law-add-tuple-Ring

  tuple-Ring-Group : ℕ → Group l
  pr1 (tuple-Ring-Group n) = tuple-Ring-Semigroup R n
  pr2 (tuple-Ring-Group n) = is-group-tuple-Ring n

  tuple-Ring-Ab : ℕ → Ab l
  pr1 (tuple-Ring-Ab n) = tuple-Ring-Group n
  pr2 (tuple-Ring-Ab n) = commutative-add-tuple-Ring R
```

## See also

- For the [module](ring-theory.modules-rings.md) of tuples on rings, see
  [`linear-algebra.scalar-multiplication-tuples-on-rings`](
