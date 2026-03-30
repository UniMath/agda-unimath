# Removing elements in finite sequences

```agda
module lists.remove-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

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
    (n : ℕ) →
    (i : Fin (succ-ℕ n)) →
    fin-sequence A (succ-ℕ n) →
    fin-sequence A n
  remove-at-fin-sequence zero-ℕ _ u ()
  remove-at-fin-sequence (succ-ℕ n) (inl x) u (inl y) =
    remove-at-fin-sequence n x (tail-fin-sequence (succ-ℕ n) u) y
  remove-at-fin-sequence (succ-ℕ n) (inl x) u (inr y) =
    head-fin-sequence (succ-ℕ n) u
  remove-at-fin-sequence (succ-ℕ n) (inr x) u =
    tail-fin-sequence (succ-ℕ n) u
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
  htpy-map-remove-at-fin-sequence (succ-ℕ n) (inl x) u (inl y) =
    htpy-map-remove-at-fin-sequence n x
      ( tail-fin-sequence (succ-ℕ n) u)
      ( y)
  htpy-map-remove-at-fin-sequence (succ-ℕ n) (inl x) u (inr y) = refl
  htpy-map-remove-at-fin-sequence (succ-ℕ n) (inr x) u k = refl
```
