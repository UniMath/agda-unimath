# Integer multiples of elements in large abelian groups

```agda
module group-theory.integer-multiples-of-elements-large-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.integer-powers-of-elements-large-groups
open import group-theory.large-abelian-groups
open import group-theory.multiples-of-elements-large-abelian-groups
```

</details>

## Idea

The integer
{{#concept "multiplication" Disambiguation="integer multiplication of elements of large abelian groups" Agda=int-multiple-Large-Ab}}
on a [large abelian group](group-theory.large-abelian-groups.md) is the map
`k x ↦ kx`, which is defined by
[iteratively](foundation.iterating-automorphisms.md) adding `x` with itself an
[integer](elementary-number-theory.integers.md) `k` times.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  int-multiple-Large-Ab :
    {l : Level} → ℤ → type-Large-Ab G l → type-Large-Ab G l
  int-multiple-Large-Ab =
    int-power-Large-Group (large-group-Large-Ab G)
```

## Properties

### The canonical embedding of natural numbers in the integers preserves powers

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    int-multiple-int-Large-Ab :
      {l : Level} (n : ℕ) (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G (int-ℕ n) x ＝ multiple-Large-Ab G n x
    int-multiple-int-Large-Ab =
      int-power-int-Large-Group (large-group-Large-Ab G)
```

### The integer multiple `0x` is `0`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    left-zero-law-int-multiple-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G zero-ℤ x ＝ raise-zero-Large-Ab G l
    left-zero-law-int-multiple-Large-Ab =
      int-power-zero-Large-Group (large-group-Large-Ab G)
```

### The integer multiple `1x` is `x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    int-multiple-one-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G one-ℤ x ＝ x
    int-multiple-one-Large-Ab =
      int-power-one-Large-Group (large-group-Large-Ab G)
```

### The integer multiple `(-1)x` is `-x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    int-multiple-neg-one-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G neg-one-ℤ x ＝ neg-Large-Ab G x
    int-multiple-neg-one-Large-Ab =
      int-power-neg-one-Large-Group (large-group-Large-Ab G)
```

### `(m + n) ∙ x = m ∙ x + n ∙ x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    right-distributive-int-multiple-add-Large-Ab :
      {l : Level} (x : type-Large-Ab G l) (m n : ℤ) →
      int-multiple-Large-Ab G (m +ℤ n) x ＝
      add-Large-Ab G (int-multiple-Large-Ab G m x) (int-multiple-Large-Ab G n x)
    right-distributive-int-multiple-add-Large-Ab =
      distributive-int-power-add-Large-Group (large-group-Large-Ab G)
```

### `(-n) ∙ x ＝ -(n ∙ x)`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    int-multiple-neg-Large-Ab :
      {l : Level} (n : ℤ) (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G (neg-ℤ n) x ＝
      neg-Large-Ab G (int-multiple-Large-Ab G n x)
    int-multiple-neg-Large-Ab =
      int-power-neg-Large-Group (large-group-Large-Ab G)
```

### `(k + 1) ∙ x = k ∙ x + x = x + k ∙ x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    int-multiple-succ-Large-Ab :
      {l : Level} (n : ℤ) (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G (succ-ℤ n) x ＝
      add-Large-Ab G (int-multiple-Large-Ab G n x) x
    int-multiple-succ-Large-Ab =
      int-power-succ-Large-Group (large-group-Large-Ab G)

    int-multiple-succ-Large-Ab' :
      {l : Level} (n : ℤ) (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G (succ-ℤ n) x ＝
      add-Large-Ab G x (int-multiple-Large-Ab G n x)
    int-multiple-succ-Large-Ab' =
      int-power-succ-Large-Group' (large-group-Large-Ab G)
```

### `(k - 1) ∙ x = k ∙ x - x = -x + k ∙ x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    int-multiple-pred-Large-Ab :
      {l : Level} (n : ℤ) (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G (pred-ℤ n) x ＝
      add-Large-Ab G (int-multiple-Large-Ab G n x) (neg-Large-Ab G x)
    int-multiple-pred-Large-Ab =
      int-power-pred-Large-Group (large-group-Large-Ab G)

    int-multiple-pred-Large-Ab' :
      {l : Level} (n : ℤ) (x : type-Large-Ab G l) →
      int-multiple-Large-Ab G (pred-ℤ n) x ＝
      add-Large-Ab G (neg-Large-Ab G x) (int-multiple-Large-Ab G n x)
    int-multiple-pred-Large-Ab' =
      int-power-pred-Large-Group' (large-group-Large-Ab G)
```

### `k ∙ 0 = 0`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    right-zero-law-int-multiple-Large-Ab :
      (l : Level) (k : ℤ) →
      int-multiple-Large-Ab G k (raise-zero-Large-Ab G l) ＝
      raise-zero-Large-Ab G l
    right-zero-law-int-multiple-Large-Ab =
      raise-int-power-unit-Large-Group (large-group-Large-Ab G)
```

### Integer multiples distribute over the sum of `x` and `y`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    left-distributive-int-multiple-add-Large-Ab :
      {l1 l2 : Level} (k : ℤ) →
      (x : type-Large-Ab G l1) (y : type-Large-Ab G l2) →
      int-multiple-Large-Ab G k (add-Large-Ab G x y) ＝
      add-Large-Ab G (int-multiple-Large-Ab G k x) (int-multiple-Large-Ab G k y)
    left-distributive-int-multiple-add-Large-Ab k x y =
      distributive-int-power-mul-Large-Group
        ( large-group-Large-Ab G)
        ( k)
        ( x)
        ( y)
        ( commutative-add-Large-Ab G x y)
```

### Multiples by products of integers are iterated integer multiples

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (G : Large-Ab α β)
  where

  abstract
    int-multiple-mul-Large-Group :
      {l1 : Level} (k l : ℤ) (x : type-Large-Ab G l1) →
      int-multiple-Large-Ab G (k *ℤ l) x ＝
      int-multiple-Large-Ab G l (int-multiple-Large-Ab G k x)
    int-multiple-mul-Large-Group =
      int-power-mul-Large-Group (large-group-Large-Ab G)
```

## See also

- [Natural multiples of elements of large abelian groups](group-theory.multiples-of-elements-large-abelian-groups.md)
- [Integer multiples of elements of small abelian groups](group-theory.integer-multiples-of-elements-abelian-groups.md)
