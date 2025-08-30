# Finite sequences

```agda
module lists.finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sequences
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "finite sequence" Agda=fin-sequence}} of length `n` is a map from
the [standard finite type](univalent-combinatorics.standard-finite-types.md) of
cardinality `n`, `Fin n`, to `A`. These are
[equivalent](lists.equivalence-tuples-finite-sequences.md) to the related
concept of [tuples](lists.tuples.md), but are structured like
[arrays](lists.arrays.md) instead of [lists](lists.lists.md).

## Definition

```agda
fin-sequence : {l : Level} → UU l → ℕ → UU l
fin-sequence A n = Fin n → A

module _
  {l : Level} {A : UU l}
  where

  empty-fin-sequence : fin-sequence A 0
  empty-fin-sequence ()

  head-fin-sequence : (n : ℕ) → fin-sequence A (succ-ℕ n) → A
  head-fin-sequence n v = v (inr star)

  tail-fin-sequence :
    (n : ℕ) → fin-sequence A (succ-ℕ n) → fin-sequence A n
  tail-fin-sequence n v = v ∘ (inl-Fin n)

  cons-fin-sequence :
    (n : ℕ) → A → fin-sequence A n → fin-sequence A (succ-ℕ n)
  cons-fin-sequence n a v (inl x) = v x
  cons-fin-sequence n a v (inr x) = a

  snoc-fin-sequence :
    (n : ℕ) → fin-sequence A n → A → fin-sequence A (succ-ℕ n)
  snoc-fin-sequence zero-ℕ v a i = a
  snoc-fin-sequence (succ-ℕ n) v a (inl x) =
    snoc-fin-sequence n (tail-fin-sequence n v) a x
  snoc-fin-sequence (succ-ℕ n) v a (inr x) = head-fin-sequence n v

  revert-fin-sequence :
    (n : ℕ) → fin-sequence A n → fin-sequence A n
  revert-fin-sequence n v i = v (opposite-Fin n i)

  in-fin-sequence : (n : ℕ) → A → fin-sequence A n → UU l
  in-fin-sequence n a v = Σ (Fin n) (λ k → a ＝ v k)

  index-in-fin-sequence :
    (n : ℕ) (x : A) (v : fin-sequence A n) →
    in-fin-sequence n x v → Fin n
  index-in-fin-sequence n x v I = pr1 I

  eq-component-fin-sequence-index-in-fin-sequence :
    (n : ℕ) (x : A) (v : fin-sequence A n) (I : in-fin-sequence n x v) →
    x ＝ v (index-in-fin-sequence n x v I)
  eq-component-fin-sequence-index-in-fin-sequence n x v I = pr2 I
```

## Properties

### The type of finite sequences of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-fin-sequence :
    (k : 𝕋) (n : ℕ) → is-trunc k A → is-trunc k (fin-sequence A n)
  is-trunc-fin-sequence k n H = is-trunc-function-type k H
```

### The type of finite sequences of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-fin-sequence : (n : ℕ) → is-set A → is-set (fin-sequence A n)
  is-set-fin-sequence = is-trunc-fin-sequence zero-𝕋

fin-sequence-Set : {l : Level} → Set l → ℕ → Set l
pr1 (fin-sequence-Set A n) = fin-sequence (type-Set A) n
pr2 (fin-sequence-Set A n) = is-set-fin-sequence n (is-set-type-Set A)
```

### Adding the tail to the head gives the same finite sequence

```agda
module _
  {l : Level} {A : UU l}
  where
  htpy-cons-head-tail-fin-sequence :
    ( n : ℕ) →
    ( v : fin-sequence A (succ-ℕ n)) →
    ( cons-fin-sequence n
      ( head-fin-sequence n v)
      ( tail-fin-sequence n v)) ~
      ( v)
  htpy-cons-head-tail-fin-sequence n v (inl x) = refl
  htpy-cons-head-tail-fin-sequence n v (inr star) = refl

  cons-head-tail-fin-sequence :
    ( n : ℕ) →
    ( v : fin-sequence A (succ-ℕ n)) →
    ( cons-fin-sequence n
      ( head-fin-sequence n v)
      ( tail-fin-sequence n v)) ＝
      ( v)
  cons-head-tail-fin-sequence n v =
    eq-htpy (htpy-cons-head-tail-fin-sequence n v)
```

### Any sequence `u` in a type determines a sequence of finite sequences `(i : Fin n) ↦ u i`

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  fin-sequence-sequence : (n : ℕ) → fin-sequence A n
  fin-sequence-sequence n i = u (nat-Fin n i)

  eq-fin-sequence-sequence :
    (n : ℕ) → fin-sequence-sequence (succ-ℕ n) (neg-one-Fin n) ＝ u n
  eq-fin-sequence-sequence n = refl

  eq-zero-fin-sequence-sequence :
    (n : ℕ) → fin-sequence-sequence (succ-ℕ n) (zero-Fin n) ＝ u 0
  eq-zero-fin-sequence-sequence n = ap u (is-zero-nat-zero-Fin {n})

  eq-skip-zero-fin-sequence-sequence :
    (n : ℕ) (i : Fin n) →
    fin-sequence-sequence (succ-ℕ n) (skip-zero-Fin n i) ＝
    u (succ-ℕ (nat-Fin n i))
  eq-skip-zero-fin-sequence-sequence n i = ap u (nat-skip-zero-Fin n i)

module _
  {l : Level} {A : UU l} (u v : sequence A) (H : u ~ v)
  where

  htpy-fin-sequence-sequence :
    (n : ℕ) → fin-sequence-sequence u n ~ fin-sequence-sequence v n
  htpy-fin-sequence-sequence n i = H (nat-Fin n i)
```

## See also

- [Sequences](foundation.sequences.md)
