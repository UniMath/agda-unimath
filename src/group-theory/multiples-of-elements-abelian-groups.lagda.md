# Multiples of elements in abelian groups

```agda
module group-theory.multiples-of-elements-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.sets

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.powers-of-elements-groups
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

### The predicate of being a natural multiple of an element in an abelian group

We say that an element `y` **is a multiple** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`nx ＝ y`.

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-multiple-of-element-prop-Ab :
    (x y : type-Ab A) → Prop l
  is-multiple-of-element-prop-Ab =
    is-power-of-element-prop-Group (group-Ab A)

  is-multiple-of-element-Ab :
    (x y : type-Ab A) → UU l
  is-multiple-of-element-Ab =
    is-power-of-element-Group (group-Ab A)

  is-prop-is-multiple-of-element-Ab :
    (x y : type-Ab A) →
    is-prop (is-multiple-of-element-Ab x y)
  is-prop-is-multiple-of-element-Ab =
    is-prop-is-power-of-element-Group (group-Ab A)
```

## Properties

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

### The multiply-by-`n` homomorphism `A → A`

```agda
module _
  {l : Level} (A : Ab l)
  where

  multiple-hom-Ab : (n : ℕ) → hom-Ab A A
  pr1 (multiple-hom-Ab n) = multiple-Ab A n
  pr2 (multiple-hom-Ab n) {x} {y} = left-distributive-multiple-add-Ab A n
```
