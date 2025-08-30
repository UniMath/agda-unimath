# Finite sequences in commutative semigroups

```agda
module linear-algebra.finite-sequences-in-commutative-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-semigroups
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-semigroups
```

</details>

## Idea

Given a [commutative semigroup](group-theory.commutative-semigroups.md) `G`, the
type `fin-sequence n G` of [finite sequences](lists.finite-sequences.md) of
length `n` of elements of `G` is a commutative semigroup given by componentwise
addition.

We use additive terminology for vectors, as is standard in linear algebra
contexts, despite using multiplicative terminology for semigroups.

## Definitions

```agda
module _
  {l : Level} (M : Commutative-Semigroup l)
  where

  fin-sequence-type-Commutative-Semigroup : ℕ → UU l
  fin-sequence-type-Commutative-Semigroup =
    fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup M)

  head-fin-sequence-type-Commutative-Semigroup :
    (n : ℕ) → fin-sequence-type-Commutative-Semigroup (succ-ℕ n) →
    type-Commutative-Semigroup M
  head-fin-sequence-type-Commutative-Semigroup =
    head-fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup M)

  tail-fin-sequence-type-Commutative-Semigroup :
    (n : ℕ) → fin-sequence-type-Commutative-Semigroup (succ-ℕ n) →
    fin-sequence-type-Commutative-Semigroup n
  tail-fin-sequence-type-Commutative-Semigroup =
    tail-fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup M)

  cons-fin-sequence-type-Commutative-Semigroup :
    (n : ℕ) → type-Commutative-Semigroup M →
    fin-sequence-type-Commutative-Semigroup n →
    fin-sequence-type-Commutative-Semigroup (succ-ℕ n)
  cons-fin-sequence-type-Commutative-Semigroup =
    cons-fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup M)

  snoc-fin-sequence-type-Commutative-Semigroup :
    (n : ℕ) → fin-sequence-type-Commutative-Semigroup n →
    type-Commutative-Semigroup M →
    fin-sequence-type-Commutative-Semigroup (succ-ℕ n)
  snoc-fin-sequence-type-Commutative-Semigroup =
    snoc-fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup M)
```

### Pointwise addition of finite sequences in a commutative semigroup

```agda
module _
  {l : Level} (M : Commutative-Semigroup l)
  where

  add-fin-sequence-type-Commutative-Semigroup :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Semigroup M n) →
    fin-sequence-type-Commutative-Semigroup M n
  add-fin-sequence-type-Commutative-Semigroup =
    add-fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup M)

  associative-add-fin-sequence-type-Commutative-Semigroup :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Commutative-Semigroup M n) →
    ( add-fin-sequence-type-Commutative-Semigroup n
      ( add-fin-sequence-type-Commutative-Semigroup n v1 v2) v3) ＝
    ( add-fin-sequence-type-Commutative-Semigroup n v1
      ( add-fin-sequence-type-Commutative-Semigroup n v2 v3))
  associative-add-fin-sequence-type-Commutative-Semigroup =
    associative-add-fin-sequence-type-Semigroup
      ( semigroup-Commutative-Semigroup M)

  semigroup-fin-sequence-type-Commutative-Semigroup : ℕ → Semigroup l
  semigroup-fin-sequence-type-Commutative-Semigroup =
    semigroup-fin-sequence-type-Semigroup (semigroup-Commutative-Semigroup M)

  commutative-add-fin-sequence-type-Commutative-Semigroup :
    (n : ℕ) (v w : fin-sequence-type-Commutative-Semigroup M n) →
    add-fin-sequence-type-Commutative-Semigroup n v w ＝
    add-fin-sequence-type-Commutative-Semigroup n w v
  commutative-add-fin-sequence-type-Commutative-Semigroup _ _ _ =
    eq-htpy (λ k → commutative-mul-Commutative-Semigroup M _ _)

  commutative-semigroup-fin-sequence-type-Commutative-Semigroup :
    ℕ → Commutative-Semigroup l
  commutative-semigroup-fin-sequence-type-Commutative-Semigroup n =
    semigroup-fin-sequence-type-Commutative-Semigroup n ,
    commutative-add-fin-sequence-type-Commutative-Semigroup n
```
