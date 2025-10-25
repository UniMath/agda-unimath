# Finite sequences in semigroups

```agda
module linear-algebra.finite-sequences-in-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.semigroups

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
```

</details>

## Idea

Given a [semigroup](group-theory.monoids.md) `G`, the type `fin-sequence n G` of
[finite sequences](lists.finite-sequences.md) of length `n` of elements of `G`
is a semigroup given by componentwise multiplication.

We use additive terminology for finite sequences, as is standard in linear
algebra contexts, despite using multiplicative terminology for semigroups.

## Definitions

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  fin-sequence-type-Semigroup : ℕ → UU l
  fin-sequence-type-Semigroup = fin-sequence (type-Semigroup G)

  head-fin-sequence-type-Semigroup :
    (n : ℕ) → fin-sequence-type-Semigroup (succ-ℕ n) → type-Semigroup G
  head-fin-sequence-type-Semigroup n v = head-fin-sequence n v

  tail-fin-sequence-type-Semigroup :
    (n : ℕ) → fin-sequence-type-Semigroup (succ-ℕ n) →
    fin-sequence-type-Semigroup n
  tail-fin-sequence-type-Semigroup = tail-fin-sequence

  cons-fin-sequence-type-Semigroup :
    (n : ℕ) → type-Semigroup G →
    fin-sequence-type-Semigroup n →
    fin-sequence-type-Semigroup (succ-ℕ n)
  cons-fin-sequence-type-Semigroup = cons-fin-sequence

  snoc-fin-sequence-type-Semigroup :
    (n : ℕ) → fin-sequence-type-Semigroup n → type-Semigroup G →
    fin-sequence-type-Semigroup (succ-ℕ n)
  snoc-fin-sequence-type-Semigroup = snoc-fin-sequence
```

### Pointwise addition of finite sequences in a semigroup

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  add-fin-sequence-type-Semigroup :
    (n : ℕ) (v w : fin-sequence-type-Semigroup G n) →
    fin-sequence-type-Semigroup G n
  add-fin-sequence-type-Semigroup n =
    binary-map-fin-sequence n (mul-Semigroup G)

  associative-add-fin-sequence-type-Semigroup :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Semigroup G n) →
    add-fin-sequence-type-Semigroup n
      ( add-fin-sequence-type-Semigroup n v1 v2)
      ( v3) ＝
    add-fin-sequence-type-Semigroup n
      ( v1)
      ( add-fin-sequence-type-Semigroup n v2 v3)
  associative-add-fin-sequence-type-Semigroup n v1 v2 v3 =
    eq-htpy (λ i → associative-mul-Semigroup G (v1 i) (v2 i) (v3 i))

  semigroup-fin-sequence-type-Semigroup : ℕ → Semigroup l
  pr1 (semigroup-fin-sequence-type-Semigroup n) =
    fin-sequence-Set (set-Semigroup G) n
  pr1 (pr2 (semigroup-fin-sequence-type-Semigroup n)) =
    add-fin-sequence-type-Semigroup n
  pr2 (pr2 (semigroup-fin-sequence-type-Semigroup n)) =
    associative-add-fin-sequence-type-Semigroup n
```
