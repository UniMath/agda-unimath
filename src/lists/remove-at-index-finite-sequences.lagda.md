# Removing elements in finite sequences

```agda
module lists.remove-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.skipping-two-elements-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`
and a type `A`, the
{{#concept "removing map" Disambiguation="of finite sequences" Agda=remove-at-fin-sequence}}
at [index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)` is
the map `Aⁿ⁺¹ → Aⁿ` that **removes** the `i`th coordinate:

```text
  (x₀,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xₙ) ↦ (x₀,...xᵢ₋₁,xᵢ₊₁,...,xₙ)
```

## Definitions

### Removing an element at an index

```agda
module _
  {l : Level} {A : UU l}
  where

  remove-at-fin-sequence :
    (n : ℕ)
    (i : Fin (succ-ℕ n)) →
    fin-sequence A (succ-ℕ n) →
    fin-sequence A n
  remove-at-fin-sequence n i u j = u (skip-Fin n i j)
```

### Removing two elements at distinct indices

```agda
module _
  {l : Level} {A : UU l}
  where

  remove-at-two-indices-fin-sequence :
    (n : ℕ) (i j : Fin (n +ℕ 2)) → i ≠ j →
    fin-sequence A (n +ℕ 2) → fin-sequence A n
  remove-at-two-indices-fin-sequence n i j i≠j u k =
    u (skip-two-Fin n i j i≠j k)
```

## Properties

### Removing is functorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  htpy-map-remove-at-fin-sequence :
    (n : ℕ) →
    (i : Fin (succ-ℕ n))
    (u : fin-sequence A (succ-ℕ n)) →
    map-fin-sequence n f (remove-at-fin-sequence n i u) ~
    remove-at-fin-sequence n i (map-fin-sequence (succ-ℕ n) f u)
  htpy-map-remove-at-fin-sequence n i u x = refl
```

### Removing indices `i` and `j` is the same as removing indices `j` and `i`

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  htpy-swap-remove-at-two-indices-fin-sequence' :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (j≠i : j ≠ i)
    (u : fin-sequence A (n +ℕ 2)) →
    remove-at-two-indices-fin-sequence n i j i≠j u ~
    remove-at-two-indices-fin-sequence n j i j≠i u
  htpy-swap-remove-at-two-indices-fin-sequence' n i j i≠j j≠i u k =
    ap u (swap-skip-two-Fin n i j i≠j j≠i k)

  htpy-swap-remove-at-two-indices-fin-sequence :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j)
    (u : fin-sequence A (n +ℕ 2)) →
    remove-at-two-indices-fin-sequence n i j i≠j u ~
    remove-at-two-indices-fin-sequence n j i (is-symmetric-nonequal i j i≠j) u
  htpy-swap-remove-at-two-indices-fin-sequence n i j i≠j =
    htpy-swap-remove-at-two-indices-fin-sequence' n i j
      ( i≠j)
      ( is-symmetric-nonequal i j i≠j)
```
