# Replacements at indices in finite sequences

```agda
module lists.replace-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.focus-at-index-finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`
and a type `A`, the
{{#concept "replacement map" Disambiguation="of finite sequences" Agda=replace-at-finite-sequence}}
at [indices](univalent-combinatorics.standard-finite-types.md) `(i j : ℕₙ)` is
the map `Aⁿ⁺¹ → Aⁿ⁺¹` that [extracts](lists.focus-at-index-finite-sequences.md)
the coordinate at `j` and inserts it at `i`:

```text
  (xₒ,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xⱼ₋₁,xⱼ,xⱼ₊₁,...,xₙ) ↦
  (xₒ,...xᵢ₋₁,xⱼ,xᵢ,xᵢ₊₁,...,xⱼ₋₁,xⱼ₊₁,...,xₙ)
```

## Definitions

### Replace elements at a pair of indices

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i j : Fin (succ-ℕ n))
  where

  replace-at-finite-sequence :
    fin-sequence A (succ-ℕ n) → fin-sequence A (succ-ℕ n)
  replace-at-finite-sequence =
    unfocus-at-finite-sequence n i ∘ focus-at-finite-sequence n j
```

## Properties

### Replacing at the same index is the identity

```agda
module _
  {l : Level} {A : UU l} (n : ℕ)
  where

  id-replace-at-finite-sequence :
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    replace-at-finite-sequence n i i u ＝ u
  id-replace-at-finite-sequence i u =
    is-retraction-focus-at-finite-sequence n i u
```

### Composing replacements

```agda
module _
  {l : Level} {A : UU l} (n : ℕ)
  where

  comp-replace-at-finite-sequence :
    (i j k : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    replace-at-finite-sequence n i j
      ( replace-at-finite-sequence n j k u) ＝
    replace-at-finite-sequence n i k u
  comp-replace-at-finite-sequence i j k u =
    ap
      ( unfocus-at-finite-sequence n i)
      ( is-section-focus-at-finite-sequence n j
        ( focus-at-finite-sequence n k u))
```

### Replacing elements is an equivalence

```agda
module _
  {l : Level} {A : UU l} (n : ℕ)
  where abstract

  is-section-replace-at-finite-sequence :
    (i j : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    replace-at-finite-sequence n i j (replace-at-finite-sequence n j i u) ＝ u
  is-section-replace-at-finite-sequence i j u =
    ( comp-replace-at-finite-sequence n i j i u) ∙
    ( id-replace-at-finite-sequence n i u)

  is-equiv-replace-at-finite-sequence :
    (i j : Fin (succ-ℕ n)) → is-equiv (replace-at-finite-sequence {A = A} n i j)
  is-equiv-replace-at-finite-sequence i j =
    is-equiv-is-invertible
      ( replace-at-finite-sequence n j i)
      ( is-section-replace-at-finite-sequence i j)
      ( is-section-replace-at-finite-sequence j i)

module _
  {l : Level} {A : UU l} (n : ℕ) (i j : Fin (succ-ℕ n))
  where

  equiv-replace-at-finite-sequence :
    fin-sequence A (succ-ℕ n) ≃ fin-sequence A (succ-ℕ n)
  equiv-replace-at-finite-sequence =
    ( replace-at-finite-sequence n i j ,
      is-equiv-replace-at-finite-sequence n i j)
```

### Focusing at a replaced element

```agda
module _
  {l : Level} {A : UU l} (n : ℕ)
  where

  compute-focus-at-replace-at-finite :
    (i j : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    focus-at-finite-sequence n i
      ( replace-at-finite-sequence n i j u) ＝
    focus-at-finite-sequence n j u
  compute-focus-at-replace-at-finite i j =
    is-section-focus-at-finite-sequence n i ∘ focus-at-finite-sequence n j
```
