# Finite sequences in abelian-groups

```agda
module linear-algebra.finite-sequences-in-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.function-abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-monoids

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given an [abelian group](group-theory.abelian-groups.md) `G`, the type
`fin-sequence n G` of [finite sequences](lists.finite-sequences.md) of length
`n` of elements of `G` is a group given by componentwise addition.

## Definitions

```agda
module _
  {l : Level} (G : Ab l)
  where

  fin-sequence-type-Ab : ℕ → UU l
  fin-sequence-type-Ab = fin-sequence (type-Ab G)

  head-fin-sequence-type-Ab :
    (n : ℕ) → fin-sequence-type-Ab (succ-ℕ n) →
    type-Ab G
  head-fin-sequence-type-Ab =
    head-fin-sequence-type-Monoid (monoid-Ab G)

  tail-fin-sequence-type-Ab :
    (n : ℕ) → fin-sequence-type-Ab (succ-ℕ n) →
    fin-sequence-type-Ab n
  tail-fin-sequence-type-Ab =
    tail-fin-sequence-type-Monoid (monoid-Ab G)

  cons-fin-sequence-type-Ab :
    (n : ℕ) → type-Ab G →
    fin-sequence-type-Ab n →
    fin-sequence-type-Ab (succ-ℕ n)
  cons-fin-sequence-type-Ab =
    cons-fin-sequence-type-Monoid (monoid-Ab G)

  snoc-fin-sequence-type-Ab :
    (n : ℕ) → fin-sequence-type-Ab n →
    type-Ab G → fin-sequence-type-Ab (succ-ℕ n)
  snoc-fin-sequence-type-Ab =
    snoc-fin-sequence-type-Monoid (monoid-Ab G)
```

### Zero finite sequences in a group

```agda
module _
  {l : Level} (G : Ab l)
  where

  zero-fin-sequence-type-Ab :
    (n : ℕ) → fin-sequence-type-Ab G n
  zero-fin-sequence-type-Ab n i = zero-Ab G
```

### Negation of finite sequences in a group

```agda
module _
  {l : Level} (G : Ab l)
  where

  neg-fin-sequence-type-Ab :
    (n : ℕ) → fin-sequence-type-Ab G n → fin-sequence-type-Ab G n
  neg-fin-sequence-type-Ab n = neg-function-Ab G (Fin n)
```

### Pointwise addition of finite sequences in a group

```agda
module _
  {l : Level} (G : Ab l)
  where

  add-fin-sequence-type-Ab :
    (n : ℕ) (v w : fin-sequence-type-Ab G n) →
    fin-sequence-type-Ab G n
  add-fin-sequence-type-Ab =
    add-fin-sequence-type-Monoid (monoid-Ab G)

  associative-add-fin-sequence-type-Ab :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Ab G n) →
    ( add-fin-sequence-type-Ab n
      ( add-fin-sequence-type-Ab n v1 v2) v3) ＝
    ( add-fin-sequence-type-Ab n v1
      ( add-fin-sequence-type-Ab n v2 v3))
  associative-add-fin-sequence-type-Ab =
    associative-add-fin-sequence-type-Monoid (monoid-Ab G)

  left-unit-law-add-fin-sequence-type-Ab :
    (n : ℕ) (v : fin-sequence-type-Ab G n) →
    add-fin-sequence-type-Ab n
      ( zero-fin-sequence-type-Ab G n) v ＝ v
  left-unit-law-add-fin-sequence-type-Ab =
    left-unit-law-add-fin-sequence-type-Monoid (monoid-Ab G)

  right-unit-law-add-fin-sequence-type-Ab :
    (n : ℕ) (v : fin-sequence-type-Ab G n) →
    add-fin-sequence-type-Ab n v
      ( zero-fin-sequence-type-Ab G n) ＝ v
  right-unit-law-add-fin-sequence-type-Ab =
    right-unit-law-add-fin-sequence-type-Monoid (monoid-Ab G)

  left-inverse-law-add-fin-sequence-type-Ab :
    (n : ℕ) (v : fin-sequence-type-Ab G n) →
    add-fin-sequence-type-Ab n
      ( neg-fin-sequence-type-Ab G n v)
      ( v) ＝
    zero-fin-sequence-type-Ab G n
  left-inverse-law-add-fin-sequence-type-Ab n =
    left-inverse-law-add-function-Ab G (Fin n)

  right-inverse-law-add-fin-sequence-type-Ab :
    (n : ℕ) (v : fin-sequence-type-Ab G n) →
    add-fin-sequence-type-Ab n
      ( v)
      ( neg-fin-sequence-type-Ab G n v) ＝
    zero-fin-sequence-type-Ab G n
  right-inverse-law-add-fin-sequence-type-Ab n =
    right-inverse-law-add-function-Ab G (Fin n)

  commutative-add-fin-sequence-type-Ab :
    (n : ℕ) → (v w : fin-sequence-type-Ab G n) →
    add-fin-sequence-type-Ab n v w ＝ add-fin-sequence-type-Ab n w v
  commutative-add-fin-sequence-type-Ab n = commutative-add-function-Ab G (Fin n)

  ab-fin-sequence-type-Ab : ℕ → Ab l
  ab-fin-sequence-type-Ab n = function-Ab G (Fin n)
```
