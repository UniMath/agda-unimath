# Powers of elements in groups

```agda
module group-theory.powers-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.powers-of-elements-monoids

open import structured-types.initial-pointed-type-equipped-with-automorphism
```

</details>

## Idea

The power operation on a group is the map `n x ↦ xⁿ`, which is defined by
iteratively multiplying `x` with itself `n` times. We define this operation
where `n` ranges over the natural numbers, as well as where `n` ranges over the
integers.

## Definition

### Powers by natural numbers of group elements

```agda
module _
  {l : Level} (G : Group l)
  where

  power-Group : ℕ → type-Group G → type-Group G
  power-Group = power-Monoid (monoid-Group G)
```

### Iterating multiplication by `g`

```agda
module _
  {l : Level} (G : Group l)
  where

  iterated-multiplication-by-element-Group :
    type-Group G → ℤ → type-Group G → type-Group G
  iterated-multiplication-by-element-Group g k =
    map-iterate-automorphism-ℤ k (equiv-mul-Group G g)
```

### Powers by integers of group elements

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-Group : ℤ → type-Group G → type-Group G
  integer-power-Group k g =
    map-iterate-automorphism-ℤ k (equiv-mul-Group G g) (unit-Group G)
```

## Properties

### Associativity of iterated multiplication by a group element

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  associative-iterated-multiplication-by-element-Group :
    (k : ℤ) (h1 h2 : type-Group G) →
    iterated-multiplication-by-element-Group G g k (mul-Group G h1 h2) ＝
    mul-Group G (iterated-multiplication-by-element-Group G g k h1) h2
  associative-iterated-multiplication-by-element-Group
    ( inl zero-ℕ) h1 h2 =
    inv (associative-mul-Group G (inv-Group G g) h1 h2)
  associative-iterated-multiplication-by-element-Group
    ( inl (succ-ℕ x)) h1 h2 =
    ( ap
      ( mul-Group G (inv-Group G g))
      ( associative-iterated-multiplication-by-element-Group
        ( inl x)
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G
        ( inv-Group G g)
        ( iterated-multiplication-by-element-Group G g (inl x) h1)
        ( h2)))
  associative-iterated-multiplication-by-element-Group
    ( inr (inl star)) h1 h2 =
    refl
  associative-iterated-multiplication-by-element-Group
    ( inr (inr zero-ℕ)) h1 h2 =
    inv (associative-mul-Group G g h1 h2)
  associative-iterated-multiplication-by-element-Group
    ( inr (inr (succ-ℕ x))) h1 h2 =
    ( ap
      ( mul-Group G g)
      ( associative-iterated-multiplication-by-element-Group
        ( inr (inr x))
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G g
        ( iterated-multiplication-by-element-Group G g (inr (inr x)) h1)
        ( h2)))
```

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (G : Group l)
  where

  power-unit-Group :
    (n : ℕ) → power-Group G n (unit-Group G) ＝ unit-Group G
  power-unit-Group = power-unit-Monoid (monoid-Group G)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (G : Group l)
  where

  power-succ-Group :
    (n : ℕ) (x : type-Group G) →
    power-Group G (succ-ℕ n) x ＝ mul-Group G (power-Group G n x) x
  power-succ-Group = power-succ-Monoid (monoid-Group G)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (G : Group l)
  where

  power-succ-Group' :
    (n : ℕ) (x : type-Group G) →
    power-Group G (succ-ℕ n) x ＝ mul-Group G x (power-Group G n x)
  power-succ-Group' = power-succ-Monoid' (monoid-Group G)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (G : Group l)
  where

  distributive-power-add-Group :
    (m n : ℕ) {x : type-Group G} →
    power-Group G (m +ℕ n) x ＝
    mul-Group G (power-Group G m x) (power-Group G n x)
  distributive-power-add-Group = distributive-power-add-Monoid (monoid-Group G)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (G : Group l)
  where

  commute-powers-Group' :
    (n : ℕ) {x y : type-Group G} →
    ( mul-Group G x y ＝ mul-Group G y x) →
    ( mul-Group G (power-Group G n x) y) ＝
    ( mul-Group G y (power-Group G n x))
  commute-powers-Group' = commute-powers-Monoid' (monoid-Group G)

  commute-powers-Group :
    (m n : ℕ) {x y : type-Group G} →
    ( mul-Group G x y ＝ mul-Group G y x) →
    ( mul-Group G (power-Group G m x) (power-Group G n y)) ＝
    ( mul-Group G (power-Group G n y) (power-Group G m x))
  commute-powers-Group = commute-powers-Monoid (monoid-Group G)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (G : Group l)
  where

  distributive-power-mul-Group :
    (n : ℕ) {x y : type-Group G} →
    (H : mul-Group G x y ＝ mul-Group G y x) →
    power-Group G n (mul-Group G x y) ＝
    mul-Group G (power-Group G n x) (power-Group G n y)
  distributive-power-mul-Group =
    distributive-power-mul-Monoid (monoid-Group G)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (G : Group l)
  where

  power-mul-Group :
    (m n : ℕ) {x : type-Group G} →
    power-Group G (m *ℕ n) x ＝ power-Group G n (power-Group G m x)
  power-mul-Group = power-mul-Monoid (monoid-Group G)
```

### `integer-power-Group G (int-ℕ n) g ＝ power-Group G n g`

```agda
module _
  {l : Level} (G : Group l)
  where

  integer-power-int-Group :
    (n : ℕ) (g : type-Group G) →
    integer-power-Group G (int-ℕ n) g ＝ power-Group G n g
  integer-power-int-Group zero-ℕ g = refl
  integer-power-int-Group (succ-ℕ zero-ℕ) g = right-unit-law-mul-Group G g
  integer-power-int-Group (succ-ℕ (succ-ℕ n)) g =
    ( ap (mul-Group G g) (integer-power-int-Group (succ-ℕ n) g)) ∙
    ( inv (power-succ-Group' G (succ-ℕ n) g))
```

### The integer power `x⁰` is the unit of the group

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  integer-power-zero-Group :
    integer-power-Group G zero-ℤ g ＝ unit-Group G
  integer-power-zero-Group =
    preserves-point-map-ℤ-Pointed-Type-With-Aut
      ( pointed-type-with-aut-Group G g)
```

### The integer power `gˣ⁺ʸ` computes to `gˣgʸ`

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  distributive-integer-power-add-Group :
    (x y : ℤ) →
    ( integer-power-Group G (x +ℤ y) g) ＝
    ( mul-Group G
      ( integer-power-Group G x g)
      ( integer-power-Group G y g))
  distributive-integer-power-add-Group x y =
    ( iterate-automorphism-add-ℤ x y (equiv-mul-Group G g) (unit-Group G)) ∙
    ( ( ap
        ( iterated-multiplication-by-element-Group G g x)
        ( inv (left-unit-law-mul-Group G
          ( integer-power-Group G y g)))) ∙
      ( associative-iterated-multiplication-by-element-Group G g x
        ( unit-Group G)
        ( integer-power-Group G y g)))
```

### Group homomorphisms preserve powers

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H)
  where

  preserves-powers-hom-Group :
    (n : ℕ) (x : type-Group G) →
    map-hom-Group G H f (power-Group G n x) ＝
    power-Group H n (map-hom-Group G H f x)
  preserves-powers-hom-Group =
    preserves-powers-hom-Monoid
      ( monoid-Group G)
      ( monoid-Group H)
      ( hom-monoid-hom-Group G H f)

  preserves-integer-powers-hom-Group :
    (k : ℤ) (x : type-Group G) →
    map-hom-Group G H f (integer-power-Group G k x) ＝
    integer-power-Group H k (map-hom-Group G H f x)
  preserves-integer-powers-hom-Group (inl zero-ℕ) x =
    ( preserves-mul-hom-Group G H f (inv-Group G x) (unit-Group G)) ∙
    ( ap-mul-Group H
      ( preserves-inv-hom-Group G H f x)
      ( preserves-unit-hom-Group G H f))
  preserves-integer-powers-hom-Group (inl (succ-ℕ k)) x =
    ( preserves-mul-hom-Group G H f
      ( inv-Group G x)
      ( integer-power-Group G (inl k) x)) ∙
    ( ap-mul-Group H
      ( preserves-inv-hom-Group G H f x)
      ( preserves-integer-powers-hom-Group (inl k) x))
  preserves-integer-powers-hom-Group (inr (inl star)) x =
    preserves-unit-hom-Group G H f
  preserves-integer-powers-hom-Group (inr (inr zero-ℕ)) x =
    ( preserves-mul-hom-Group G H f x (unit-Group G)) ∙
    ( ap (mul-Group H (map-hom-Group G H f x)) (preserves-unit-hom-Group G H f))
  preserves-integer-powers-hom-Group (inr (inr (succ-ℕ k))) x =
    ( preserves-mul-hom-Group G H f x (integer-power-Group G (inr (inr k)) x)) ∙
    ( ap
      ( mul-Group H (map-hom-Group G H f x))
      ( preserves-integer-powers-hom-Group (inr (inr k)) x))

module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H)
  where

  eq-integer-power-hom-Group :
    (g : type-hom-Group G H) (k : ℤ) (x : type-Group G) →
    ( map-hom-Group G H f x ＝ map-hom-Group G H g x) →
    ( map-hom-Group G H f (integer-power-Group G k x) ＝
      map-hom-Group G H g (integer-power-Group G k x))
  eq-integer-power-hom-Group g k x p =
    ( preserves-integer-powers-hom-Group G H f k x) ∙
    ( ( ap (integer-power-Group H k) p) ∙
      ( inv (preserves-integer-powers-hom-Group G H g k x)))
```
