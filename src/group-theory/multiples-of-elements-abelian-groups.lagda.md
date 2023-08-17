# Multiples of elements in abelian groups

```agda
module group-theory.multiples-of-elements-abelian-groups where
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
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.powers-of-elements-groups

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
  {l : Level} (A : Ab l)
  where

  multiple-nat-Ab : ℕ → type-Ab A → type-Ab A
  multiple-nat-Ab = power-nat-Group (group-Ab A)
```

### Iterating multiplication by `g`

```agda
module _
  {l : Level} (A : Ab l)
  where

  iterated-addition-by-element-Ab :
    type-Ab A → ℤ → type-Ab A → type-Ab A
  iterated-addition-by-element-Ab g k =
    map-iterate-automorphism-ℤ k (equiv-add-Ab A g)
```

### Multiples by integers of group elements

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-int-Ab : ℤ → type-Ab A → type-Ab A
  multiple-int-Ab k g =
    map-iterate-automorphism-ℤ k (equiv-add-Ab A g) (zero-Ab A)
```

## Properties

### Associativity of iterated multiplication by a group element

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  associative-iterated-addition-by-element-Ab :
    (k : ℤ) (h1 h2 : type-Ab A) →
    iterated-addition-by-element-Ab A a k (add-Ab A h1 h2) ＝
    add-Ab A (iterated-addition-by-element-Ab A a k h1) h2
  associative-iterated-addition-by-element-Ab =
    associative-iterated-multiplication-by-element-Group (group-Ab A) a
```

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-nat-zero-Ab :
    (n : ℕ) → multiple-nat-Ab A n (zero-Ab A) ＝ zero-Ab A
  multiple-nat-zero-Ab = power-nat-unit-Group (group-Ab A)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-succ-nat-Ab :
    (n : ℕ) (x : type-Ab A) →
    multiple-nat-Ab A (succ-ℕ n) x ＝ add-Ab A (multiple-nat-Ab A n x) x
  multiple-succ-nat-Ab = power-succ-nat-Group (group-Ab A)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-succ-nat-Ab' :
    (n : ℕ) (x : type-Ab A) →
    multiple-nat-Ab A (succ-ℕ n) x ＝ add-Ab A x (multiple-nat-Ab A n x)
  multiple-succ-nat-Ab' = power-succ-nat-Group' (group-Ab A)
```

### Multiples by sums of natural numbers are products of multiples

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-add-nat-Ab :
    (m n : ℕ) {x : type-Ab A} →
    multiple-nat-Ab A (m +ℕ n) x ＝
    add-Ab A (multiple-nat-Ab A m x) (multiple-nat-Ab A n x)
  multiple-add-nat-Ab = power-add-nat-Group (group-Ab A)
```

### If `x` commutes with `y` then so do their multiples

```agda
module _
  {l : Level} (A : Ab l)
  where

  commute-multiples-nat-Ab' :
    (n : ℕ) {x y : type-Ab A} →
    ( add-Ab A x y ＝ add-Ab A y x) →
    ( add-Ab A (multiple-nat-Ab A n x) y) ＝
    ( add-Ab A y (multiple-nat-Ab A n x))
  commute-multiples-nat-Ab' = commute-powers-nat-Group' (group-Ab A)

  commute-multiples-nat-Ab :
    (m n : ℕ) {x y : type-Ab A} →
    ( add-Ab A x y ＝ add-Ab A y x) →
    ( add-Ab A (multiple-nat-Ab A m x) (multiple-nat-Ab A n y)) ＝
    ( add-Ab A (multiple-nat-Ab A n y) (multiple-nat-Ab A m x))
  commute-multiples-nat-Ab = commute-powers-nat-Group (group-Ab A)
```

### If `x` commutes with `y`, then multiples distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (A : Ab l)
  where

  distributive-multiple-nat-add-Ab :
    (n : ℕ) {x y : type-Ab A} →
    (H : add-Ab A x y ＝ add-Ab A y x) →
    multiple-nat-Ab A n (add-Ab A x y) ＝
    add-Ab A (multiple-nat-Ab A n x) (multiple-nat-Ab A n y)
  distributive-multiple-nat-add-Ab =
    distributive-power-nat-mul-Group (group-Ab A)
```

### Multiples by products of natural numbers are iterated multiples

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-mul-nat-Ab :
    (m n : ℕ) {x : type-Ab A} →
    multiple-nat-Ab A (m *ℕ n) x ＝ multiple-nat-Ab A n (multiple-nat-Ab A m x)
  multiple-mul-nat-Ab = power-mul-nat-Group (group-Ab A)
```

### `multiple-int-Ab A (int-ℕ n) g ＝ multiple-nat-Ab A n g`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-int-nat-Ab :
    (n : ℕ) (g : type-Ab A) →
    multiple-int-Ab A (int-ℕ n) g ＝ multiple-nat-Ab A n g
  multiple-int-nat-Ab zero-ℕ g = refl
  multiple-int-nat-Ab (succ-ℕ zero-ℕ) g = right-unit-law-add-Ab A g
  multiple-int-nat-Ab (succ-ℕ (succ-ℕ n)) g =
    ( ap (add-Ab A g) (multiple-int-nat-Ab (succ-ℕ n) g)) ∙
    ( inv (multiple-succ-nat-Ab' A (succ-ℕ n) g))
```

### The integer multiple `x⁰` is the unit of the group

```agda
module _
  {l : Level} (A : Ab l) (g : type-Ab A)
  where

  multiple-zero-int-Ab :
    multiple-int-Ab A zero-ℤ g ＝ zero-Ab A
  multiple-zero-int-Ab = integer-power-zero-Group (group-Ab A) g
```

### The integer multiple `gˣ⁺ʸ` computes to `gˣgʸ`

```agda
module _
  {l : Level} (A : Ab l) (g : type-Ab A)
  where

  multiple-add-int-Ab :
    (x y : ℤ) →
    ( multiple-int-Ab A (x +ℤ y) g) ＝
    ( add-Ab A
      ( multiple-int-Ab A x g)
      ( multiple-int-Ab A y g))
  multiple-add-int-Ab = integer-power-add-Group (group-Ab A) g
```

### Homomorphisms of abelian groups preserve multiples

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B)
  where

  preserves-multiples-hom-Ab :
    (n : ℕ) (x : type-Ab A) →
    map-hom-Ab A B f (multiple-nat-Ab A n x) ＝
    multiple-nat-Ab B n (map-hom-Ab A B f x)
  preserves-multiples-hom-Ab =
    preserves-powers-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)
```
