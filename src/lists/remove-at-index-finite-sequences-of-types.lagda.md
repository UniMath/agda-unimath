# Removing elements of dependent finite sequences

```agda
module lists.remove-at-index-finite-sequences-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.negated-equality
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.finite-sequences-of-types
open import lists.remove-at-index-finite-sequences

open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.skipping-two-elements-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`
and a finite sequence of types `A₀, A₁, ..., Aₙ`, the
{{#concept "removing map" Disambiguation="of dependent finite sequences" Agda=remove-at-Π-fin-sequence}}
at [index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)` is
the map taking an element of `Πᵢ Aᵢ` that **removes** the `i`th coordinate:

```text
  (x₀,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xₙ) ↦ (x₀,...xᵢ₋₁,xᵢ₊₁,...,xₙ)
```

## Definition

### Removing at one index

```agda
remove-at-Π-fin-sequence :
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (succ-ℕ n))
  (i : Fin (succ-ℕ n)) →
  Π-fin-sequence (succ-ℕ n) A →
  Π-fin-sequence n (remove-at-fin-sequence n i A)
remove-at-Π-fin-sequence n A i u j = u (skip-Fin n i j)
```

### Removing at two indices

```agda
remove-at-two-indices-Π-fin-sequence :
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (n +ℕ 2))
  (i j : Fin (n +ℕ 2))
  (i≠j : i ≠ j) →
  Π-fin-sequence (n +ℕ 2) A →
  Π-fin-sequence n (remove-at-two-indices-fin-sequence n i j i≠j A)
remove-at-two-indices-Π-fin-sequence n A i j i≠j u k =
  u (skip-two-Fin n i j i≠j k)
```
