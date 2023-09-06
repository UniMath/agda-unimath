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

The multiplication operation on an
[abelian group](group-theory.abelian-groups.md) is the map `n x ↦ n · x`, which
is defined by [iteratively](foundation.iterating-functions.md) adding `x` with
itself `n` times. We define this operation where `n` ranges over the
[natural numbers](elementary-number-theory.natural-numbers.md), as well as where
`n` ranges over the [integers](elementary-number-theory.integers.md).

## Definition

### Natural number multiples of abelian group elements

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-Ab : ℕ → type-Ab A → type-Ab A
  multiple-Ab = power-Group (group-Ab A)
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

### Integer Multiplication with group elements

```agda
module _
  {l : Level} (A : Ab l)
  where

  integer-multiple-Ab : ℤ → type-Ab A → type-Ab A
  integer-multiple-Ab k g =
    map-iterate-automorphism-ℤ k (equiv-add-Ab A g) (zero-Ab A)
```

## Properties

### Associativity of iterated addition by a group element

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

### `n · 0 ＝ 0`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-zero-Ab :
    (n : ℕ) → multiple-Ab A n (zero-Ab A) ＝ zero-Ab A
  multiple-zero-Ab = power-unit-Group (group-Ab A)
```

### `(n + 1) · x = n · x + x`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-succ-Ab :
    (n : ℕ) (x : type-Ab A) →
    multiple-Ab A (succ-ℕ n) x ＝ add-Ab A (multiple-Ab A n x) x
  multiple-succ-Ab = power-succ-Group (group-Ab A)
```

### `(n + 1) · x ＝ x + n · x`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-succ-Ab' :
    (n : ℕ) (x : type-Ab A) →
    multiple-Ab A (succ-ℕ n) x ＝ add-Ab A x (multiple-Ab A n x)
  multiple-succ-Ab' = power-succ-Group' (group-Ab A)
```

### Multiples by sums of natural numbers are products of multiples

```agda
module _
  {l : Level} (A : Ab l)
  where

  right-distributive-multiple-add-Ab :
    (m n : ℕ) {x : type-Ab A} →
    multiple-Ab A (m +ℕ n) x ＝
    add-Ab A (multiple-Ab A m x) (multiple-Ab A n x)
  right-distributive-multiple-add-Ab = distributive-power-add-Group (group-Ab A)
```

### Multiples distribute over the sum of `x` and `y`

```agda
module _
  {l : Level} (A : Ab l)
  where

  left-distributive-multiple-add-Ab :
    (n : ℕ) {x y : type-Ab A} →
    multiple-Ab A n (add-Ab A x y) ＝
    add-Ab A (multiple-Ab A n x) (multiple-Ab A n y)
  left-distributive-multiple-add-Ab n =
    distributive-power-mul-Group (group-Ab A) n (commutative-add-Ab A _ _)
```

### Multiples by products of natural numbers are iterated multiples

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-mul-Ab :
    (m n : ℕ) {x : type-Ab A} →
    multiple-Ab A (m *ℕ n) x ＝ multiple-Ab A n (multiple-Ab A m x)
  multiple-mul-Ab = power-mul-Group (group-Ab A)
```

### `integer-multiple-Ab A (int-ℕ n) g ＝ multiple-Ab A n g`

```agda
module _
  {l : Level} (A : Ab l)
  where

  integer-multiple-int-Ab :
    (n : ℕ) (g : type-Ab A) →
    integer-multiple-Ab A (int-ℕ n) g ＝ multiple-Ab A n g
  integer-multiple-int-Ab zero-ℕ g = refl
  integer-multiple-int-Ab (succ-ℕ zero-ℕ) g = right-unit-law-add-Ab A g
  integer-multiple-int-Ab (succ-ℕ (succ-ℕ n)) g =
    ( ap (add-Ab A g) (integer-multiple-int-Ab (succ-ℕ n) g)) ∙
    ( inv (multiple-succ-Ab' A (succ-ℕ n) g))
```

### The integer multiple `0 · x` is the unit of the group

```agda
module _
  {l : Level} (A : Ab l) (g : type-Ab A)
  where

  integer-multiple-zero-Ab :
    integer-multiple-Ab A zero-ℤ g ＝ zero-Ab A
  integer-multiple-zero-Ab = integer-power-zero-Group (group-Ab A) g
```

### The integer multiple `(x+y)g` computes to `xg+yg`

```agda
module _
  {l : Level} (A : Ab l) (g : type-Ab A)
  where

  distributive-integer-multiple-add-Ab :
    (x y : ℤ) →
    ( integer-multiple-Ab A (x +ℤ y) g) ＝
    ( add-Ab A
      ( integer-multiple-Ab A x g)
      ( integer-multiple-Ab A y g))
  distributive-integer-multiple-add-Ab =
    distributive-integer-power-add-Group (group-Ab A) g
```

### Homomorphisms of abelian groups preserve multiples

```agda
module _
  {l1 l2 : Level} (A : Ab l1) (B : Ab l2) (f : type-hom-Ab A B)
  where

  preserves-multiples-hom-Ab :
    (n : ℕ) (x : type-Ab A) →
    map-hom-Ab A B f (multiple-Ab A n x) ＝
    multiple-Ab B n (map-hom-Ab A B f x)
  preserves-multiples-hom-Ab =
    preserves-powers-hom-Group
      ( group-Ab A)
      ( group-Ab B)
      ( f)
```
