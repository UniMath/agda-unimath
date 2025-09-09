# Linear combinations

```agda
module linear-algebra.linear-combinations where
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
[ring](ring-theory.rings.md) `R`. Given a tuple `(r_1, ..., r_n)` of elements of
`R` and a tuple `(x_1, ..., x_n)` of elements of `M`, a
{{#concept "linear combination" Agda=linear-combination-left-module-Ring}} of
these tuples is the sum `r_1 * x_1 + ... + r_n * x_n`.

## Definitions

### Linear combinations in a left module over a ring

```agda
linear-combination-left-module-Ring :
  {l1 l2 : Level}
  {n : ℕ} →
  (R : Ring l1)
  (M : left-module-Ring l2 R) →
  tuple (type-Ring R) n →
  tuple (type-left-module-Ring R M) n →
  type-left-module-Ring R M
linear-combination-left-module-Ring R M empty-tuple empty-tuple =
  zero-left-module-Ring R M
linear-combination-left-module-Ring R M (r ∷ scalars) (x ∷ vectors) =
  add-left-module-Ring R M
    ( linear-combination-left-module-Ring R M scalars vectors)
    ( mul-left-module-Ring R M r x)
```

## Properties

### Left distributivity law for multiplication

```agda
left-distributive-law-mul-linear-combination-left-module-Ring :
  {l1 l2 : Level}
  {n : ℕ} →
  (R : Ring l1) →
  (M : left-module-Ring l2 R)
  (r : type-Ring R) →
  (scalars : tuple (type-Ring R) n) →
  (vectors : tuple (type-left-module-Ring R M) n) →
  mul-left-module-Ring R M
    ( r)
    ( linear-combination-left-module-Ring R M scalars vectors) ＝
  linear-combination-left-module-Ring R M
    ( map-tuple (mul-Ring R r) scalars)
    ( vectors)
left-distributive-law-mul-linear-combination-left-module-Ring
  R M r empty-tuple empty-tuple =
    equational-reasoning
      mul-left-module-Ring R M r
        ( linear-combination-left-module-Ring R M empty-tuple empty-tuple)
      ＝
        mul-left-module-Ring R M r (zero-left-module-Ring R M)
        by refl
      ＝
        zero-left-module-Ring R M
        by right-zero-law-mul-left-module-Ring R M r
      ＝
        linear-combination-left-module-Ring R M empty-tuple empty-tuple
        by refl
left-distributive-law-mul-linear-combination-left-module-Ring
  R M r (s ∷ scalars) (x ∷ vectors) =
    equational-reasoning
      mul-left-module-Ring R M r
        ( linear-combination-left-module-Ring R M (s ∷ scalars) (x ∷ vectors))
      ＝
        mul-left-module-Ring R M r
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M scalars vectors)
            ( mul-left-module-Ring R M s x))
        by refl
      ＝
        add-left-module-Ring R M
          ( mul-left-module-Ring R M r
            ( linear-combination-left-module-Ring R M scalars vectors))
          ( mul-left-module-Ring R M r (mul-left-module-Ring R M s x))
        by left-distributive-mul-add-left-module-Ring R M r
          ( linear-combination-left-module-Ring R M scalars vectors)
          ( mul-left-module-Ring R M s x)
      ＝
        add-left-module-Ring R M
          ( mul-left-module-Ring R M r
            ( linear-combination-left-module-Ring R M scalars vectors))
          ( mul-left-module-Ring R M (mul-Ring R r s) x)
        by ap
          ( λ y →
            add-left-module-Ring R M
              ( mul-left-module-Ring R M r
                ( linear-combination-left-module-Ring R M scalars vectors))
              ( y))
          (inv (associative-mul-left-module-Ring R M r s x))
      ＝
        add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M
            ( map-tuple (mul-Ring R r) scalars)
            ( vectors))
          ( mul-left-module-Ring R M (mul-Ring R r s) x)
        by ap
          ( λ y →
            add-left-module-Ring R M
              ( y)
              ( mul-left-module-Ring R M (mul-Ring R r s) x))
          ( left-distributive-law-mul-linear-combination-left-module-Ring R M r
            ( scalars)
            ( vectors))
      ＝
        linear-combination-left-module-Ring R M
          ( map-tuple (mul-Ring R r) (s ∷ scalars))
          ( x ∷ vectors)
        by refl
```

### Concatenation is addition

```agda
concatenation-is-addition-linear-combination-left-module-Ring :
  {l1 l2 : Level}
  {n m : ℕ} →
  (R : Ring l1) →
  (M : left-module-Ring l2 R)
  (scalars-a : tuple (type-Ring R) n) →
  (vectors-a : tuple (type-left-module-Ring R M) n) →
  (scalars-b : tuple (type-Ring R) m) →
  (vectors-b : tuple (type-left-module-Ring R M) m) →
  linear-combination-left-module-Ring R M
    ( concat-tuple scalars-a scalars-b)
    ( concat-tuple vectors-a vectors-b) ＝
  add-left-module-Ring R M
    ( linear-combination-left-module-Ring R M scalars-a vectors-a)
    ( linear-combination-left-module-Ring R M scalars-b vectors-b)
concatenation-is-addition-linear-combination-left-module-Ring
  R M empty-tuple empty-tuple scalars-b vectors-b =
    equational-reasoning
      linear-combination-left-module-Ring R M
        ( concat-tuple empty-tuple scalars-b)
        ( concat-tuple empty-tuple vectors-b)
      ＝
        linear-combination-left-module-Ring R M scalars-b vectors-b
        by refl
      ＝
        add-left-module-Ring R M
          ( zero-left-module-Ring R M)
          ( linear-combination-left-module-Ring R M scalars-b vectors-b)
        by inv
          ( left-unit-law-add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M scalars-b vectors-b))
      ＝
        add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M empty-tuple empty-tuple)
          ( linear-combination-left-module-Ring R M scalars-b vectors-b)
        by refl
concatenation-is-addition-linear-combination-left-module-Ring
  R M (r ∷ scalars-a) (x ∷ vectors-a) scalars-b vectors-b =
    equational-reasoning
      linear-combination-left-module-Ring R M
        ( concat-tuple (r ∷ scalars-a) scalars-b)
        ( concat-tuple (x ∷ vectors-a) vectors-b)
      ＝
        linear-combination-left-module-Ring R M
          ( r ∷ (concat-tuple scalars-a scalars-b))
          ( x ∷ (concat-tuple vectors-a vectors-b))
        by refl
      ＝
        add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M
            ( concat-tuple scalars-a scalars-b)
            ( concat-tuple vectors-a vectors-b))
          ( mul-left-module-Ring R M r x)
        by refl
      ＝
        add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( linear-combination-left-module-Ring R M
              ( scalars-b)
              ( vectors-b)))
          ( mul-left-module-Ring R M r x)
        by ap
          ( λ z → add-left-module-Ring R M z (mul-left-module-Ring R M r x))
          ( concatenation-is-addition-linear-combination-left-module-Ring R M
            ( scalars-a)
            ( vectors-a)
            ( scalars-b)
            ( vectors-b))
      ＝
        add-left-module-Ring R M
          ( mul-left-module-Ring R M r x)
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( linear-combination-left-module-Ring R M
              ( scalars-b)
              ( vectors-b)))
        by commutative-add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( linear-combination-left-module-Ring R M
              ( scalars-b)
              ( vectors-b)))
          ( mul-left-module-Ring R M r x)
      ＝
        add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( mul-left-module-Ring R M r x)
            ( linear-combination-left-module-Ring R M
              ( scalars-a)
              ( vectors-a)))
          ( linear-combination-left-module-Ring R M
            ( scalars-b)
            ( vectors-b))
        by inv
          ( associative-add-left-module-Ring R M
            ( mul-left-module-Ring R M r x)
            ( linear-combination-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( linear-combination-left-module-Ring R M
              ( scalars-b)
              ( vectors-b)))
      ＝
        add-left-module-Ring R M
          ( add-left-module-Ring R M
            ( linear-combination-left-module-Ring R M
              ( scalars-a)
              ( vectors-a))
            ( mul-left-module-Ring R M r x))
          ( linear-combination-left-module-Ring R M
            ( scalars-b)
            ( vectors-b))
        by ap
          ( λ y → add-left-module-Ring R M y
            ( linear-combination-left-module-Ring R M
              ( scalars-b)
              ( vectors-b)))
          ( commutative-add-left-module-Ring R M
            ( mul-left-module-Ring R M r x)
            ( linear-combination-left-module-Ring R M
              ( scalars-a)
              ( vectors-a)))
      ＝
        add-left-module-Ring R M
          ( linear-combination-left-module-Ring R M
            ( r ∷ scalars-a)
            ( x ∷ vectors-a))
          ( linear-combination-left-module-Ring R M
            ( scalars-b)
            ( vectors-b))
        by refl
```
