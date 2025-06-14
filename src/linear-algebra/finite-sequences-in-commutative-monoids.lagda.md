# Finite sequences in commutative monoids

```agda
module linear-algebra.finite-sequences-in-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-monoids
```

</details>

## Idea

Given a [commutative monoid](group-theory.commutative-monoids.md) `M`, the type
`fin-sequence n M` of [finite sequences](lists.finite-sequences.md) of length
`n` of elements of `M` is a commutative monoid given by componentwise addition.

We use additive terminology for vectors, as is standard in linear algebra
contexts, despite using multiplicative terminology for monoids.

## Definitions

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  fin-sequence-type-Commutative-Monoid : ℕ → UU l
  fin-sequence-type-Commutative-Monoid =
    fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  head-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) → fin-sequence-type-Commutative-Monoid (succ-ℕ n) →
    type-Commutative-Monoid M
  head-fin-sequence-type-Commutative-Monoid =
    head-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  tail-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) → fin-sequence-type-Commutative-Monoid (succ-ℕ n) →
    fin-sequence-type-Commutative-Monoid n
  tail-fin-sequence-type-Commutative-Monoid =
    tail-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  cons-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) → type-Commutative-Monoid M →
    fin-sequence-type-Commutative-Monoid n →
    fin-sequence-type-Commutative-Monoid (succ-ℕ n)
  cons-fin-sequence-type-Commutative-Monoid =
    cons-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  snoc-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) → fin-sequence-type-Commutative-Monoid n →
    type-Commutative-Monoid M → fin-sequence-type-Commutative-Monoid (succ-ℕ n)
  snoc-fin-sequence-type-Commutative-Monoid =
    snoc-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Zero finite sequences in a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  zero-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) → fin-sequence-type-Commutative-Monoid M n
  zero-fin-sequence-type-Commutative-Monoid n i = unit-Commutative-Monoid M
```

### Pointwise addition of finite sequences in a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  add-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Monoid M n) →
    fin-sequence-type-Commutative-Monoid M n
  add-fin-sequence-type-Commutative-Monoid =
    add-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  associative-add-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Commutative-Monoid M n) →
    ( add-fin-sequence-type-Commutative-Monoid n
      ( add-fin-sequence-type-Commutative-Monoid n v1 v2) v3) ＝
    ( add-fin-sequence-type-Commutative-Monoid n v1
      ( add-fin-sequence-type-Commutative-Monoid n v2 v3))
  associative-add-fin-sequence-type-Commutative-Monoid =
    associative-add-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  semigroup-fin-sequence-type-Commutative-Monoid : ℕ → Semigroup l
  semigroup-fin-sequence-type-Commutative-Monoid =
    semigroup-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  left-unit-law-add-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (v : fin-sequence-type-Commutative-Monoid M n) →
    add-fin-sequence-type-Commutative-Monoid n
      ( zero-fin-sequence-type-Commutative-Monoid M n) v ＝ v
  left-unit-law-add-fin-sequence-type-Commutative-Monoid =
    left-unit-law-add-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  right-unit-law-add-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (v : fin-sequence-type-Commutative-Monoid M n) →
    add-fin-sequence-type-Commutative-Monoid n v
      ( zero-fin-sequence-type-Commutative-Monoid M n) ＝ v
  right-unit-law-add-fin-sequence-type-Commutative-Monoid =
    right-unit-law-add-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  monoid-fin-sequence-type-Commutative-Monoid : ℕ → Monoid l
  monoid-fin-sequence-type-Commutative-Monoid =
    monoid-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  commutative-add-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Monoid M n) →
    add-fin-sequence-type-Commutative-Monoid n v w ＝
    add-fin-sequence-type-Commutative-Monoid n w v
  commutative-add-fin-sequence-type-Commutative-Monoid _ _ _ =
    eq-htpy (λ k → commutative-mul-Commutative-Monoid M _ _)

  commutative-monoid-fin-sequence-type-Commutative-Monoid :
    ℕ → Commutative-Monoid l
  commutative-monoid-fin-sequence-type-Commutative-Monoid n =
    monoid-fin-sequence-type-Commutative-Monoid n ,
    commutative-add-fin-sequence-type-Commutative-Monoid n
```
