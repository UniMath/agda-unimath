# Multiples of elements in large abelian groups

```agda
module group-theory.multiples-of-elements-large-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.large-abelian-groups
open import group-theory.powers-of-elements-large-groups
```

</details>

## Idea

The
{{#concept "multiplication" Disambiguation="natural multiple of elements of large abelian groups" Agda=multiple-Large-Ab}}
operation on a [large abelian group](group-theory.large-abelian-groups.md) is
the map `n x ↦ n · x`, which is defined by
[iteratively](foundation.iterating-functions.md) adding `x` with itself `n`
times. This file describes this operation where `n` ranges over the
[natural numbers](elementary-number-theory.natural-numbers.md).

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  multiple-Large-Ab : {l : Level} → ℕ → type-Large-Ab G l → type-Large-Ab G l
  multiple-Large-Ab = power-Large-Group (large-group-Large-Ab G)
```

## Properties

### `n · 0 ＝ 0`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    raise-multiple-zero-Large-Ab :
      (l : Level) (n : ℕ) →
      multiple-Large-Ab G n (raise-zero-Large-Ab G l) ＝ raise-zero-Large-Ab G l
    raise-multiple-zero-Large-Ab =
      raise-power-unit-Large-Group (large-group-Large-Ab G)
```

### `(n + 1) ∙ x ＝ n ∙ x + x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    multiple-succ-Large-Ab :
      {l : Level} (n : ℕ) (x : type-Large-Ab G l) →
      multiple-Large-Ab G (succ-ℕ n) x ＝
      add-Large-Ab G (multiple-Large-Ab G n x) x
    multiple-succ-Large-Ab = power-succ-Large-Group (large-group-Large-Ab G)
```

### `(n + 1) ∙ x ＝ x + n ∙ x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    multiple-succ-Large-Ab' :
      {l : Level} (n : ℕ) (x : type-Large-Ab G l) →
      multiple-Large-Ab G (succ-ℕ n) x ＝
      add-Large-Ab G x (multiple-Large-Ab G n x)
    multiple-succ-Large-Ab' = power-succ-Large-Group' (large-group-Large-Ab G)
```

### Multiples by sums of natural numbers are sums of multiples

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    right-distributive-multiple-add-Large-Ab :
      {l : Level} (m n : ℕ) {x : type-Large-Ab G l} →
      multiple-Large-Ab G (m +ℕ n) x ＝
      add-Large-Ab G (multiple-Large-Ab G m x) (multiple-Large-Ab G n x)
    right-distributive-multiple-add-Large-Ab =
      distributive-power-add-Large-Group (large-group-Large-Ab G)
```

### Multiples distribute over the sum of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    left-distributive-multiple-add-Large-Ab :
      {l1 l2 : Level} (n : ℕ) →
      {x : type-Large-Ab G l1} {y : type-Large-Ab G l2} →
      multiple-Large-Ab G n (add-Large-Ab G x y) ＝
      add-Large-Ab G (multiple-Large-Ab G n x) (multiple-Large-Ab G n y)
    left-distributive-multiple-add-Large-Ab n {x} {y} =
      distributive-power-mul-Large-Group
        ( large-group-Large-Ab G)
        ( n)
        ( commutative-add-Large-Ab G x y)
```

### Multiplication by products of natural numbers is iterated multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    multiple-mul-Large-Ab :
      {l : Level} (m n : ℕ) {x : type-Large-Ab G l} →
      multiple-Large-Ab G (m *ℕ n) x ＝
      multiple-Large-Ab G n (multiple-Large-Ab G m x)
    multiple-mul-Large-Ab = power-mul-Large-Group (large-group-Large-Ab G)
```

## See also

- [Integer multiples of elements of large abelian groups](group-theory.integer-multiples-of-elements-large-abelian-groups.md)
- [Multiples of elements of small abelian groups](group-theory.multiples-of-elements-abelian-groups.md)
