# Focus of finite sequences at an index

```agda
module lists.focus-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.insert-at-index-finite-sequences
open import lists.remove-at-index-finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`
and a type `A`, the [insertion map](lists.insert-at-index-finite-sequences.md)
at an [index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)`
induces an [equivalence](foundation.equivalences.md) `Aⁿ⁺¹ ≃ A × Aⁿ`

```text
  (x₀,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xₙ) ↔ (xᵢ , (x₀,...xᵢ₋₁,xᵢ₊₁,...,xₙ))
```

These are the
{{#concept "focusing equivalences" Disambiguation="of finite sequences" Agda=equiv-focus-at-fin-sequence}}
of finite sequences.

## Definitions

### Focusing a finite sequence at an index

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where

  focus-at-fin-sequence :
    fin-sequence A (succ-ℕ n) → A × fin-sequence A n
  focus-at-fin-sequence u =
    ( elem-at-fin-sequence (succ-ℕ n) i u ,
      remove-at-fin-sequence n i u)

  unfocus-at-fin-sequence :
    A × fin-sequence A n → fin-sequence A (succ-ℕ n)
  unfocus-at-fin-sequence (a , u) = insert-at-fin-sequence n a i u
```

## Properties

### Focusing a finite sequence at an index is an equivalence

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where abstract

  is-section-focus-at-fin-sequence :
    (x : A × fin-sequence A n) →
    focus-at-fin-sequence n i (unfocus-at-fin-sequence n i x) ＝ x
  is-section-focus-at-fin-sequence (a , u) =
    eq-pair
      ( compute-elem-at-insert-at-fin-sequence n a i u)
      ( eq-htpy (compute-remove-at-insert-at-fin-sequence n a i u))

  is-retraction-focus-at-fin-sequence :
    (v : fin-sequence A (succ-ℕ n)) →
    unfocus-at-fin-sequence n i (focus-at-fin-sequence n i v) ＝ v
  is-retraction-focus-at-fin-sequence =
    eq-htpy ∘ compute-insert-at-remove-at-fin-sequence n i

  is-equiv-focus-at-fin-sequence :
    is-equiv (focus-at-fin-sequence {A = A} n i)
  is-equiv-focus-at-fin-sequence =
    is-equiv-is-invertible
      ( unfocus-at-fin-sequence n i)
      ( is-section-focus-at-fin-sequence)
      ( is-retraction-focus-at-fin-sequence)

module _
  {l : Level} (A : UU l) (n : ℕ) (i : Fin (succ-ℕ n))
  where

  equiv-focus-at-fin-sequence :
    fin-sequence A (succ-ℕ n) ≃ A × fin-sequence A n
  equiv-focus-at-fin-sequence =
    (focus-at-fin-sequence n i , is-equiv-focus-at-fin-sequence n i)
```
