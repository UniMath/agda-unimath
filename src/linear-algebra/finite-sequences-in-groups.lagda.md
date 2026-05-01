# Finite sequences in groups

```agda
module linear-algebra.finite-sequences-in-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.function-groups
open import group-theory.groups

open import linear-algebra.finite-sequences-in-monoids

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [group](group-theory.groups.md) `G`, the type `fin-sequence n G` of
[finite sequences](lists.finite-sequences.md) of length `n` of elements of `G`
is a group given by componentwise addition.

We use additive terminology for vectors, as is standard in linear algebra
contexts, despite using multiplicative terminology for groups.

## Definitions

```agda
module _
  {l : Level} (G : Group l)
  where

  fin-sequence-type-Group : ℕ → UU l
  fin-sequence-type-Group =
    fin-sequence-type-Monoid (monoid-Group G)

  head-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group (succ-ℕ n) →
    type-Group G
  head-fin-sequence-type-Group =
    head-fin-sequence-type-Monoid (monoid-Group G)

  tail-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group (succ-ℕ n) →
    fin-sequence-type-Group n
  tail-fin-sequence-type-Group =
    tail-fin-sequence-type-Monoid (monoid-Group G)

  cons-fin-sequence-type-Group :
    (n : ℕ) → type-Group G →
    fin-sequence-type-Group n →
    fin-sequence-type-Group (succ-ℕ n)
  cons-fin-sequence-type-Group =
    cons-fin-sequence-type-Monoid (monoid-Group G)

  snoc-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group n →
    type-Group G → fin-sequence-type-Group (succ-ℕ n)
  snoc-fin-sequence-type-Group =
    snoc-fin-sequence-type-Monoid (monoid-Group G)
```

### Zero finite sequences in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  zero-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group G n
  zero-fin-sequence-type-Group n i = unit-Group G
```

### Negation of finite sequences in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  neg-fin-sequence-type-Group :
    (n : ℕ) → fin-sequence-type-Group G n → fin-sequence-type-Group G n
  neg-fin-sequence-type-Group n = inv-function-Group G (Fin n)
```

### Pointwise addition of finite sequences in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  add-fin-sequence-type-Group :
    (n : ℕ) (v w : fin-sequence-type-Group G n) →
    fin-sequence-type-Group G n
  add-fin-sequence-type-Group =
    add-fin-sequence-type-Monoid (monoid-Group G)

  associative-add-fin-sequence-type-Group :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Group G n) →
    ( add-fin-sequence-type-Group n
      ( add-fin-sequence-type-Group n v1 v2) v3) ＝
    ( add-fin-sequence-type-Group n v1
      ( add-fin-sequence-type-Group n v2 v3))
  associative-add-fin-sequence-type-Group =
    associative-add-fin-sequence-type-Monoid (monoid-Group G)

  left-unit-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group n
      ( zero-fin-sequence-type-Group G n) v ＝ v
  left-unit-law-add-fin-sequence-type-Group =
    left-unit-law-add-fin-sequence-type-Monoid (monoid-Group G)

  right-unit-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group n v
      ( zero-fin-sequence-type-Group G n) ＝ v
  right-unit-law-add-fin-sequence-type-Group =
    right-unit-law-add-fin-sequence-type-Monoid (monoid-Group G)

  left-inverse-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group n
      ( neg-fin-sequence-type-Group G n v)
      ( v) ＝
    zero-fin-sequence-type-Group G n
  left-inverse-law-add-fin-sequence-type-Group n =
    left-inverse-law-mul-function-Group G (Fin n)

  right-inverse-law-add-fin-sequence-type-Group :
    (n : ℕ) (v : fin-sequence-type-Group G n) →
    add-fin-sequence-type-Group n
      ( v)
      ( neg-fin-sequence-type-Group G n v) ＝
    zero-fin-sequence-type-Group G n
  right-inverse-law-add-fin-sequence-type-Group n =
    right-inverse-law-mul-function-Group G (Fin n)

  group-fin-sequence-type-Group : ℕ → Group l
  group-fin-sequence-type-Group n = function-Group G (Fin n)
```
