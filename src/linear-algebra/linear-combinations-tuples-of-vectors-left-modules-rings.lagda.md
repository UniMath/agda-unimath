# Linear combinations of tuples of vectors in left modules over rings

```agda
module linear-algebra.linear-combinations-tuples-of-vectors-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.left-modules-rings

open import lists.concatenation-tuples
open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.rings
```

</details>

## Idea

Let `M` be a [left module](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) `R`. For any `n`-tuple of vectors (elements of `M`)
`(x_1, ..., x_n)` and any `n`-tuple of coefficients (elements of `R`)
`(r_1, ..., r_n)`, we may form the
{{#concept "linear combination" Agda=linear-combination-left-module-Ring}}
`r_1 * x_1 + ... + r_n * x_n`.

The proposition of _being_ a linear combination is formalized as being an
element of a [linear span](linear-algebra.linear-spans-left-modules-rings.md).

## Definitions

### Linear combinations of tuples of vectors in a left module over a ring

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  linear-combination-left-module-Ring :
    {n : ℕ} →
    tuple (type-Ring R) n →
    tuple (type-left-module-Ring R M) n →
    type-left-module-Ring R M
  linear-combination-left-module-Ring empty-tuple empty-tuple =
    zero-left-module-Ring R M
  linear-combination-left-module-Ring (r ∷ s) (x ∷ v) =
    add-left-module-Ring R M
      ( linear-combination-left-module-Ring s v)
      ( mul-left-module-Ring R M r x)
```

## Properties

### Left distributivity law for multiplication

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  left-distributive-law-mul-linear-combination-left-module-Ring :
    {n : ℕ}
    (r : type-Ring R) →
    (s : tuple (type-Ring R) n) →
    (v : tuple (type-left-module-Ring R M) n) →
    mul-left-module-Ring R M
      ( r)
      ( linear-combination-left-module-Ring R M s v) ＝
    linear-combination-left-module-Ring R M
      ( map-tuple (mul-Ring R r) s)
      ( v)
  left-distributive-law-mul-linear-combination-left-module-Ring
    r empty-tuple empty-tuple =
    equational-reasoning
      mul-left-module-Ring R M r
        ( linear-combination-left-module-Ring R M empty-tuple empty-tuple)
      ＝ mul-left-module-Ring R M r (zero-left-module-Ring R M)
        by refl
      ＝ zero-left-module-Ring R M
        by right-zero-law-mul-left-module-Ring R M r
      ＝ linear-combination-left-module-Ring R M empty-tuple empty-tuple
        by refl
  left-distributive-law-mul-linear-combination-left-module-Ring
    r (s₀ ∷ s) (x₀ ∷ v) =
    equational-reasoning
      mul-left-module-Ring R M r
        ( linear-combination-left-module-Ring R M (s₀ ∷ s) (x₀ ∷ v))
      ＝ mul-left-module-Ring R M r
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M s v)
            ( mul-left-module-Ring R M s₀ x₀))
        by refl
      ＝ add-left-module-Ring R M
          ( mul-left-module-Ring R M r
            ( linear-combination-left-module-Ring R M s v))
          ( mul-left-module-Ring R M r (mul-left-module-Ring R M s₀ x₀))
        by
          left-distributive-mul-add-left-module-Ring R M r
            ( linear-combination-left-module-Ring R M s v)
            ( mul-left-module-Ring R M s₀ x₀)
      ＝ add-left-module-Ring R M
          ( mul-left-module-Ring R M r
            ( linear-combination-left-module-Ring R M s v))
          ( mul-left-module-Ring R M (mul-Ring R r s₀) x₀)
        by
          ap
            ( λ y →
              add-left-module-Ring R M
                ( mul-left-module-Ring R M r
                  ( linear-combination-left-module-Ring R M s v))
                ( y))
            ( inv (associative-mul-left-module-Ring R M r s₀ x₀))
      ＝ add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M
            ( map-tuple (mul-Ring R r) s)
            ( v))
          ( mul-left-module-Ring R M (mul-Ring R r s₀) x₀)
        by
          ap
            ( λ y →
              add-left-module-Ring R M
                ( y)
                ( mul-left-module-Ring R M (mul-Ring R r s₀) x₀))
            ( left-distributive-law-mul-linear-combination-left-module-Ring r
              ( s)
              ( v))
      ＝ linear-combination-left-module-Ring R M
          ( map-tuple (mul-Ring R r) (s₀ ∷ s))
          ( x₀ ∷ v)
        by refl
```

### Concatenation is addition

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  add-concat-linear-combination-left-module-Ring :
    {n m : ℕ} →
    (s-a : tuple (type-Ring R) n) →
    (v-a : tuple (type-left-module-Ring R M) n) →
    (s-b : tuple (type-Ring R) m) →
    (v-b : tuple (type-left-module-Ring R M) m) →
    linear-combination-left-module-Ring R M
      ( concat-tuple s-a s-b)
      ( concat-tuple v-a v-b) ＝
    add-left-module-Ring R M
      ( linear-combination-left-module-Ring R M s-a v-a)
      ( linear-combination-left-module-Ring R M s-b v-b)
  add-concat-linear-combination-left-module-Ring
    empty-tuple empty-tuple s-b v-b =
    equational-reasoning
      linear-combination-left-module-Ring R M
        ( concat-tuple empty-tuple s-b)
        ( concat-tuple empty-tuple v-b)
      ＝ linear-combination-left-module-Ring R M s-b v-b
        by refl
      ＝ add-left-module-Ring R M
          ( zero-left-module-Ring R M)
          ( linear-combination-left-module-Ring R M s-b v-b)
        by
          inv
            ( left-unit-law-add-left-module-Ring R M
              ( linear-combination-left-module-Ring R M s-b v-b))
      ＝ add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M empty-tuple empty-tuple)
          ( linear-combination-left-module-Ring R M s-b v-b)
        by refl
  add-concat-linear-combination-left-module-Ring
    (r ∷ s-a) (x ∷ v-a) s-b v-b =
    equational-reasoning
      linear-combination-left-module-Ring R M
        ( concat-tuple (r ∷ s-a) s-b)
        ( concat-tuple (x ∷ v-a) v-b)
      ＝ linear-combination-left-module-Ring R M
          ( r ∷ (concat-tuple s-a s-b))
          ( x ∷ (concat-tuple v-a v-b))
        by refl
      ＝ add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M
            ( concat-tuple s-a s-b)
            ( concat-tuple v-a v-b))
          ( mul-left-module-Ring R M r x)
        by refl
      ＝ add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M
              ( s-a)
              ( v-a))
            ( linear-combination-left-module-Ring R M
              ( s-b)
              ( v-b)))
          ( mul-left-module-Ring R M r x)
        by
          ap
            ( λ z → add-left-module-Ring R M z (mul-left-module-Ring R M r x))
            ( add-concat-linear-combination-left-module-Ring
              ( s-a)
              ( v-a)
              ( s-b)
              ( v-b))
      ＝ add-left-module-Ring R M
          ( mul-left-module-Ring R M r x)
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M
              ( s-a)
              ( v-a))
            ( linear-combination-left-module-Ring R M
              ( s-b)
              ( v-b)))
        by
          commutative-add-left-module-Ring R M
            ( add-left-module-Ring R M
              ( linear-combination-left-module-Ring R M
                ( s-a)
                ( v-a))
              ( linear-combination-left-module-Ring R M
                ( s-b)
                ( v-b)))
            ( mul-left-module-Ring R M r x)
      ＝ add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( mul-left-module-Ring R M r x)
            ( linear-combination-left-module-Ring R M
              ( s-a)
              ( v-a)))
          ( linear-combination-left-module-Ring R M
            ( s-b)
            ( v-b))
        by
          inv
            ( associative-add-left-module-Ring R M
              ( mul-left-module-Ring R M r x)
              ( linear-combination-left-module-Ring R M
                ( s-a)
                ( v-a))
              ( linear-combination-left-module-Ring R M
                ( s-b)
                ( v-b)))
      ＝ add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M
              ( s-a)
              ( v-a))
            ( mul-left-module-Ring R M r x))
          ( linear-combination-left-module-Ring R M
            ( s-b)
            ( v-b))
        by
          ap
            ( λ y → add-left-module-Ring R M y
              ( linear-combination-left-module-Ring R M
                ( s-b)
                ( v-b)))
            ( commutative-add-left-module-Ring R M
              ( mul-left-module-Ring R M r x)
              ( linear-combination-left-module-Ring R M
                ( s-a)
                ( v-a)))
      ＝ add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M
            ( r ∷ s-a)
            ( x ∷ v-a))
          ( linear-combination-left-module-Ring R M
            ( s-b)
            ( v-b))
        by refl
```
