# Replacing elements of finite sequences

```agda
module lists.replace-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.replace-at-index-finite-sequences-of-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n` and a
type `A`, the
{{#concept "replacement map" Disambiguation="of finite sequences" Agda=replace-at-fin-sequence}}
of an element `x : A` at an
[index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)` is the
map taking an element of `Aⁿ` that **replaces** the `i`th coordinate with `x`:

```text
  (x₀,...,xₙ) ↦ (x₀,...xᵢ₋₁,x,xᵢ₊₁,...,xₙ)
```

## Definition

```agda
replace-at-fin-sequence :
  {l : Level} {A : UU l} (n : ℕ) →
  Fin (succ-ℕ n) → A → fin-sequence A (succ-ℕ n) → fin-sequence A (succ-ℕ n)
replace-at-fin-sequence {A = A} n = replace-at-Π-fin-sequence n (λ _ → A)
```

## Properties

### The element at the replaced index is the replaced element

```agda
abstract
  compute-elem-at-replace-at-fin-sequence :
    {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n)) (x : A) →
    (u : fin-sequence A (succ-ℕ n)) →
    replace-at-fin-sequence n i x u i ＝ x
  compute-elem-at-replace-at-fin-sequence {A = A} n =
    compute-elem-at-replace-at-Π-fin-sequence n (λ _ → A)
```

### Other indices are fixed by replacement at one index

```agda
abstract
  compute-elem-at-fixed-point-replace-at-fin-sequence :
    {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n)) (x : A) →
    (u : fin-sequence A (succ-ℕ n)) (j : Fin (succ-ℕ n)) → i ≠ j →
    replace-at-fin-sequence n i x u j ＝ u j
  compute-elem-at-fixed-point-replace-at-fin-sequence {A = A} n =
    compute-elem-at-fixed-point-replace-at-Π-fin-sequence n (λ _ → A)
```

### Replacing elements at two distinct indices can be done in either order

```agda
abstract
  htpy-swap-replace-at-fin-sequence :
    {l : Level} {A : UU l} (n : ℕ) (i j : Fin (n +ℕ 2)) → i ≠ j →
    (x y : A) (u : fin-sequence A (n +ℕ 2)) →
    replace-at-fin-sequence (succ-ℕ n) i x
      ( replace-at-fin-sequence (succ-ℕ n) j y u) ~
    replace-at-fin-sequence (succ-ℕ n) j y
      ( replace-at-fin-sequence (succ-ℕ n) i x u)
  htpy-swap-replace-at-fin-sequence {A = A} n =
    htpy-swap-replace-at-Π-fin-sequence n (λ _ → A)
```
