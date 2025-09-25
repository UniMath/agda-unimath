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
open import foundation.coproduct-types

open import foundation-core.identity-types

open import univalent-combinatorics.standard-finite-types

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
{{#concept "linear combination" Agda=linear-combination-tuple-left-module-Ring}}
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

  linear-combination-tuple-left-module-Ring :
    {n : ℕ} →
    tuple (type-Ring R) n →
    tuple (type-left-module-Ring R M) n →
    type-left-module-Ring R M
  linear-combination-tuple-left-module-Ring empty-tuple empty-tuple =
    zero-left-module-Ring R M
  linear-combination-tuple-left-module-Ring (r ∷ scalars) (x ∷ vectors) =
    add-left-module-Ring R M
      ( linear-combination-tuple-left-module-Ring scalars vectors)
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

  left-distributive-mul-linear-combination-tuple-left-module-Ring :
    {n : ℕ}
    (r : type-Ring R) →
    (scalars : tuple (type-Ring R) n) →
    (vectors : tuple (type-left-module-Ring R M) n) →
    mul-left-module-Ring R M
      ( r)
      ( linear-combination-tuple-left-module-Ring R M scalars vectors) ＝
    linear-combination-tuple-left-module-Ring R M
      ( map-tuple (mul-Ring R r) scalars)
      ( vectors)
  left-distributive-mul-linear-combination-tuple-left-module-Ring
    r empty-tuple empty-tuple =
    equational-reasoning
      mul-left-module-Ring R M r
        ( linear-combination-tuple-left-module-Ring R M empty-tuple empty-tuple)
      ＝ mul-left-module-Ring R M r (zero-left-module-Ring R M)
        by refl
      ＝ zero-left-module-Ring R M
        by right-zero-law-mul-left-module-Ring R M r
      ＝ linear-combination-tuple-left-module-Ring R M empty-tuple empty-tuple
        by refl
  left-distributive-mul-linear-combination-tuple-left-module-Ring
    r (s ∷ scalars) (x ∷ vectors) =
    equational-reasoning
      mul-left-module-Ring R M r
        ( linear-combination-tuple-left-module-Ring R M
          ( s ∷ scalars)
          ( x ∷ vectors))
      ＝ mul-left-module-Ring R M r
          ( add-left-module-Ring R M
            ( linear-combination-tuple-left-module-Ring R M scalars vectors)
            ( mul-left-module-Ring R M s x))
        by refl
      ＝ add-left-module-Ring R M
          ( mul-left-module-Ring R M r
            ( linear-combination-tuple-left-module-Ring R M scalars vectors))
          ( mul-left-module-Ring R M r (mul-left-module-Ring R M s x))
        by
          left-distributive-mul-add-left-module-Ring R M r
            ( linear-combination-tuple-left-module-Ring R M scalars vectors)
            ( mul-left-module-Ring R M s x)
      ＝ add-left-module-Ring R M
          ( mul-left-module-Ring R M r
            ( linear-combination-tuple-left-module-Ring R M scalars vectors))
          ( mul-left-module-Ring R M (mul-Ring R r s) x)
        by
          ap
            ( λ y →
              add-left-module-Ring R M
                ( mul-left-module-Ring R M r
                  ( linear-combination-tuple-left-module-Ring R M
                    ( scalars)
                    ( vectors)))
                ( y))
            ( inv (associative-mul-left-module-Ring R M r s x))
      ＝ add-left-module-Ring R M
          ( linear-combination-tuple-left-module-Ring R M
            ( map-tuple (mul-Ring R r) scalars)
            ( vectors))
          ( mul-left-module-Ring R M (mul-Ring R r s) x)
        by
          ap
            ( λ y →
              add-left-module-Ring R M
                ( y)
                ( mul-left-module-Ring R M (mul-Ring R r s) x))
            ( left-distributive-mul-linear-combination-tuple-left-module-Ring r
              ( scalars)
              ( vectors))
      ＝ linear-combination-tuple-left-module-Ring R M
          ( map-tuple (mul-Ring R r) (s ∷ scalars))
          ( x ∷ vectors)
        by refl
```

### Concatenation is addition

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  add-concat-linear-combination-tuple-left-module-Ring :
    {n m : ℕ} →
    (scalars-a : tuple (type-Ring R) n) →
    (vectors-a : tuple (type-left-module-Ring R M) n) →
    (scalars-b : tuple (type-Ring R) m) →
    (vectors-b : tuple (type-left-module-Ring R M) m) →
    linear-combination-tuple-left-module-Ring R M
      ( concat-tuple scalars-a scalars-b)
      ( concat-tuple vectors-a vectors-b) ＝
    add-left-module-Ring R M
      ( linear-combination-tuple-left-module-Ring R M scalars-a vectors-a)
      ( linear-combination-tuple-left-module-Ring R M scalars-b vectors-b)
  add-concat-linear-combination-tuple-left-module-Ring
    empty-tuple empty-tuple scalars-b vectors-b =
    equational-reasoning
      linear-combination-tuple-left-module-Ring R M
        ( concat-tuple empty-tuple scalars-b)
        ( concat-tuple empty-tuple vectors-b)
      ＝ linear-combination-tuple-left-module-Ring R M scalars-b vectors-b
        by refl
      ＝ add-left-module-Ring R M
          ( zero-left-module-Ring R M)
          ( linear-combination-tuple-left-module-Ring R M scalars-b vectors-b)
        by
          inv
            ( left-unit-law-add-left-module-Ring R M
              ( linear-combination-tuple-left-module-Ring R M
                ( scalars-b)
                ( vectors-b)))
      ＝ add-left-module-Ring R M
          ( linear-combination-tuple-left-module-Ring R M
            ( empty-tuple)
            ( empty-tuple))
          ( linear-combination-tuple-left-module-Ring R M scalars-b vectors-b)
        by refl
  add-concat-linear-combination-tuple-left-module-Ring
    (r ∷ scalars-a) (x ∷ vectors-a) scalars-b vectors-b =
    equational-reasoning
      linear-combination-tuple-left-module-Ring R M
        ( concat-tuple (r ∷ scalars-a) scalars-b)
        ( concat-tuple (x ∷ vectors-a) vectors-b)
      ＝ linear-combination-tuple-left-module-Ring R M
          ( r ∷ (concat-tuple scalars-a scalars-b))
          ( x ∷ (concat-tuple vectors-a vectors-b))
        by refl
      ＝ add-left-module-Ring R M
          ( linear-combination-tuple-left-module-Ring R M
            ( concat-tuple scalars-a scalars-b)
            ( concat-tuple vectors-a vectors-b))
          ( mul-left-module-Ring R M r x)
        by refl
      ＝ add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( linear-combination-tuple-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( linear-combination-tuple-left-module-Ring R M
              ( scalars-b)
              ( vectors-b)))
          ( mul-left-module-Ring R M r x)
        by
          ap
            ( λ z → add-left-module-Ring R M z (mul-left-module-Ring R M r x))
            ( add-concat-linear-combination-tuple-left-module-Ring
              ( scalars-a)
              ( vectors-a)
              ( scalars-b)
              ( vectors-b))
      ＝ add-left-module-Ring R M
          ( mul-left-module-Ring R M r x)
          ( add-left-module-Ring R M
            ( linear-combination-tuple-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( linear-combination-tuple-left-module-Ring R M
              ( scalars-b)
              ( vectors-b)))
        by
          commutative-add-left-module-Ring R M
            ( add-left-module-Ring R M
              ( linear-combination-tuple-left-module-Ring R M
                ( scalars-a)
                ( vectors-a))
              ( linear-combination-tuple-left-module-Ring R M
                ( scalars-b)
                ( vectors-b)))
            ( mul-left-module-Ring R M r x)
      ＝ add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( mul-left-module-Ring R M r x)
            ( linear-combination-tuple-left-module-Ring R M
              ( scalars-a)
              ( vectors-a)))
          ( linear-combination-tuple-left-module-Ring R M
            ( scalars-b)
            ( vectors-b))
        by
          inv
            ( associative-add-left-module-Ring R M
              ( mul-left-module-Ring R M r x)
              ( linear-combination-tuple-left-module-Ring R M
                ( scalars-a)
                ( vectors-a))
              ( linear-combination-tuple-left-module-Ring R M
                ( scalars-b)
                ( vectors-b)))
      ＝ add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( linear-combination-tuple-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( mul-left-module-Ring R M r x))
          ( linear-combination-tuple-left-module-Ring R M
            ( scalars-b)
            ( vectors-b))
        by
          ap
            ( λ y → add-left-module-Ring R M y
              ( linear-combination-tuple-left-module-Ring R M
                ( scalars-b)
                ( vectors-b)))
            ( commutative-add-left-module-Ring R M
              ( mul-left-module-Ring R M r x)
              ( linear-combination-tuple-left-module-Ring R M
                ( scalars-a)
                ( vectors-a)))
      ＝ add-left-module-Ring R M
          ( linear-combination-tuple-left-module-Ring R M
            ( r ∷ scalars-a)
            ( x ∷ vectors-a))
          ( linear-combination-tuple-left-module-Ring R M
            ( scalars-b)
            ( vectors-b))
        by refl
```

###

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  zero-trivial-tuple-linear-combination-tuple-left-module-Ring :
    (n : ℕ) →
    (vectors : tuple (type-left-module-Ring R M) n) →
    linear-combination-tuple-left-module-Ring R M
      ( trivial-tuple-Ring R n)
      ( vectors) ＝
    zero-left-module-Ring R M
  zero-trivial-tuple-linear-combination-tuple-left-module-Ring n empty-tuple =
    refl
  zero-trivial-tuple-linear-combination-tuple-left-module-Ring
    (succ-ℕ n) (x ∷ vectors) =
    equational-reasoning
    linear-combination-tuple-left-module-Ring R M
      ( zero-Ring R ∷ trivial-tuple-Ring R n)
      ( x ∷ vectors)
    ＝ add-left-module-Ring R M
      ( linear-combination-tuple-left-module-Ring R M
        ( trivial-tuple-Ring R n)
        ( vectors))
      ( mul-left-module-Ring R M (zero-Ring R) x)
      by refl
    ＝ add-left-module-Ring R M
      ( linear-combination-tuple-left-module-Ring R M
        ( trivial-tuple-Ring R n)
        ( vectors))
      ( zero-left-module-Ring R M)
      by
        ap
          ( λ y → add-left-module-Ring R M
            ( linear-combination-tuple-left-module-Ring R M
              ( trivial-tuple-Ring R n)
              ( vectors))
            ( y))
          (left-zero-law-mul-left-module-Ring R M x)
    ＝ add-left-module-Ring R M
      ( zero-left-module-Ring R M)
      ( zero-left-module-Ring R M)
      by
        ap
          ( λ y → add-left-module-Ring R M y (zero-left-module-Ring R M))
          ( zero-trivial-tuple-linear-combination-tuple-left-module-Ring n
            ( vectors))
    ＝ zero-left-module-Ring R M
      by left-unit-law-add-left-module-Ring R M (zero-left-module-Ring R M)
```

###

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  component-with-value-tuple-trivial-tuple-linear-combination-tuple-left-module-Ring :
    (n : ℕ) →
    (r : type-Ring R)
    (vectors : tuple (type-left-module-Ring R M) n) →
    (i : Fin n) →
    linear-combination-tuple-left-module-Ring R M
      ( with-value-tuple i r (trivial-tuple-Ring R n))
      ( vectors) ＝
    mul-left-module-Ring R M r (component-tuple n vectors i)
  component-with-value-tuple-trivial-tuple-linear-combination-tuple-left-module-Ring
    (succ-ℕ n) r (x ∷ vectors) (inr _) =
    equational-reasoning
    linear-combination-tuple-left-module-Ring R M
      ( with-value-tuple (inr _) r (trivial-tuple-Ring R (succ-ℕ n)))
      ( x ∷ vectors)
    ＝ linear-combination-tuple-left-module-Ring R M
      ( r ∷ (trivial-tuple-Ring R n))
      ( x ∷ vectors)
      by refl
    ＝ add-left-module-Ring R M
      ( linear-combination-tuple-left-module-Ring R M
        ( trivial-tuple-Ring R n)
        ( vectors))
      ( mul-left-module-Ring R M r x)
      by refl
    ＝ add-left-module-Ring R M
      ( zero-left-module-Ring R M)
      ( mul-left-module-Ring R M r x)
      by
        ap
          ( λ y → add-left-module-Ring R M y (mul-left-module-Ring R M r x))
          (zero-trivial-tuple-linear-combination-tuple-left-module-Ring R M n vectors)
    ＝ mul-left-module-Ring R M r x
      by left-unit-law-add-left-module-Ring R M (mul-left-module-Ring R M r x)
    ＝ mul-left-module-Ring R M r (component-tuple (succ-ℕ n) (x ∷ vectors) (inr _))
      by ap (λ y → mul-left-module-Ring R M r y) refl
  component-with-value-tuple-trivial-tuple-linear-combination-tuple-left-module-Ring
    (succ-ℕ n) r (x ∷ vectors) (inl i) =
    equational-reasoning
    linear-combination-tuple-left-module-Ring R M
      ( with-value-tuple (inl i) r (trivial-tuple-Ring R (succ-ℕ n)))
      ( x ∷ vectors)
    ＝ linear-combination-tuple-left-module-Ring R M
      ( zero-Ring R ∷ (with-value-tuple i r (trivial-tuple-Ring R n)))
      ( x ∷ vectors)
      by refl
    ＝ add-left-module-Ring R M
      ( linear-combination-tuple-left-module-Ring R M
        ( with-value-tuple i r (trivial-tuple-Ring R n))
        ( vectors))
      ( mul-left-module-Ring R M (zero-Ring R) x)
      by refl
    ＝ add-left-module-Ring R M
      ( linear-combination-tuple-left-module-Ring R M
        ( with-value-tuple i r (trivial-tuple-Ring R n))
        ( vectors))
      ( zero-left-module-Ring R M)
      by
        ap
          ( λ y → add-left-module-Ring R M
            ( linear-combination-tuple-left-module-Ring R M
              ( with-value-tuple i r (trivial-tuple-Ring R n))
              ( vectors))
            ( y))
          ( left-zero-law-mul-left-module-Ring R M x)
    ＝ linear-combination-tuple-left-module-Ring R M
        ( with-value-tuple i r (trivial-tuple-Ring R n))
        ( vectors)
      by right-unit-law-add-left-module-Ring R M
        ( linear-combination-tuple-left-module-Ring R M
          ( with-value-tuple i r (trivial-tuple-Ring R n))
          ( vectors))
    ＝ mul-left-module-Ring R M r (component-tuple (succ-ℕ n) (x ∷ vectors) (inl i))
      by component-with-value-tuple-trivial-tuple-linear-combination-tuple-left-module-Ring n r vectors i
```
