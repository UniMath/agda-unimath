# Replacing elements of finite sequences of types

```agda
module lists.replace-at-index-finite-sequences-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.finite-sequences-of-types
open import lists.insert-at-index-finite-sequences-of-types
open import lists.remove-at-index-finite-sequences-of-types

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n` and a
[finite sequence of types](lists.finite-sequences-of-types.md) `A₀, ..., Aₙ`,
the
{{#concept "replacement map" Disambiguation="of dependent finite sequences" Agda=replace-at-Π-fin-sequence}}
of an element `x : Aᵢ` at an
[index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)` is the
map taking an element of `Πᵢ Aᵢ` that **replaces** the `i`th coordinate with
`x`:

```text
  (x₀,...,xₙ) ↦ (x₀,...xᵢ₋₁,x,xᵢ₊₁,...,xₙ)
```

## Definition

```agda
module _
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (succ-ℕ n))
  where

  replace-at-Π-fin-sequence :
    (i : Fin (succ-ℕ n)) (uᵢ : A i) →
    Π-fin-sequence (succ-ℕ n) A → Π-fin-sequence (succ-ℕ n) A
  replace-at-Π-fin-sequence i uᵢ u =
    insert-at-Π-fin-sequence n A i uᵢ (remove-at-Π-fin-sequence n A i u)
```

## Properties

### The `i`th element of `u` after replacing the element at index `i`

```agda
module _
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (succ-ℕ n))
  where

  abstract
    compute-elem-at-replace-at-Π-fin-sequence :
      (i : Fin (succ-ℕ n)) (uᵢ : A i) (u : Π-fin-sequence (succ-ℕ n) A) →
      elem-at-Π-fin-sequence (succ-ℕ n) A i
        ( replace-at-Π-fin-sequence n A i uᵢ u) ＝
      uᵢ
    compute-elem-at-replace-at-Π-fin-sequence i uᵢ u =
      compute-elem-at-insert-at-Π-fin-sequence n A i uᵢ _
```

### Fixed points of `replace-at-Π-fin-sequence`

```agda
module _
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (succ-ℕ n))
  where

  abstract
    compute-elem-at-fixed-point-replace-at-Π-fin-sequence :
      (i : Fin (succ-ℕ n)) (uᵢ : A i) (u : Π-fin-sequence (succ-ℕ n) A)
      (j : Fin (succ-ℕ n)) → i ≠ j →
      elem-at-Π-fin-sequence (succ-ℕ n) A j
        ( replace-at-Π-fin-sequence n A i uᵢ u) ＝
      elem-at-Π-fin-sequence (succ-ℕ n) A j u
    compute-elem-at-fixed-point-replace-at-Π-fin-sequence i uᵢ u j i≠j =
      let
        (j' , snij'=j) = fiber-skip-Fin n i j i≠j
      in
        tr
          ( λ k → replace-at-Π-fin-sequence n A i uᵢ u k ＝ u k)
          ( snij'=j)
          ( compute-remove-at-insert-at-Π-fin-sequence n A i uᵢ _ j')
```

### Replacing elements at two distinct indices can be done in either order

```agda
module _
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (n +ℕ 2))
  where abstract

  htpy-swap-replace-at-Π-fin-sequence :
    (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (uᵢ : A i) (uⱼ : A j)
    (u : Π-fin-sequence (n +ℕ 2) A) →
    replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ
      ( replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u) ~
    replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ
      ( replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u)
  htpy-swap-replace-at-Π-fin-sequence i j i≠j uᵢ uⱼ u k =
    let
      j≠i = is-symmetric-nonequal i j i≠j
      uij =
        replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ
          ( replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u)
      uji =
        replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ
          ( replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u)
      case-i=k i=k =
        tr
          ( λ l → uij l ＝ uji l)
          ( i=k)
          ( equational-reasoning
            uij i
            ＝ uᵢ
              by
                compute-elem-at-replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ
                  ( replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u)
            ＝ replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u i
              by
                inv
                  ( compute-elem-at-replace-at-Π-fin-sequence
                    ( succ-ℕ n)
                    ( A)
                    ( i)
                    ( uᵢ)
                    ( u))
            ＝ uji i
              by
                inv
                  ( compute-elem-at-fixed-point-replace-at-Π-fin-sequence
                    ( succ-ℕ n)
                    ( A)
                    ( j)
                    ( uⱼ)
                    ( replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u)
                    ( i)
                    ( j≠i)))
      case-j=k j=k =
        tr
          ( λ l → uij l ＝ uji l)
          ( j=k)
          ( equational-reasoning
            uij j
            ＝ replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u j
              by
                compute-elem-at-fixed-point-replace-at-Π-fin-sequence
                  ( succ-ℕ n)
                  ( A)
                  ( i)
                  ( uᵢ)
                  ( replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u)
                  ( j)
                  ( i≠j)
            ＝ uⱼ
              by
                compute-elem-at-replace-at-Π-fin-sequence
                  ( succ-ℕ n)
                  ( A)
                  ( j)
                  ( uⱼ)
                  ( u)
            ＝ uji j
              by
                inv
                  ( compute-elem-at-replace-at-Π-fin-sequence
                    ( succ-ℕ n)
                    ( A)
                    ( j)
                    ( uⱼ)
                    ( replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u)))
      case-else i≠k j≠k =
        equational-reasoning
          uij k
          ＝ replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u k
            by
              compute-elem-at-fixed-point-replace-at-Π-fin-sequence
                ( succ-ℕ n)
                ( A)
                ( i)
                ( uᵢ)
                ( replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u)
                ( k)
                ( i≠k)
          ＝ u k
            by
              compute-elem-at-fixed-point-replace-at-Π-fin-sequence
                ( succ-ℕ n)
                ( A)
                ( j)
                ( uⱼ)
                ( u)
                ( k)
                ( j≠k)
          ＝ replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u k
            by
              inv
                ( compute-elem-at-fixed-point-replace-at-Π-fin-sequence
                  ( succ-ℕ n)
                  ( A)
                  ( i)
                  ( uᵢ)
                  ( u)
                  ( k)
                  ( i≠k))
          ＝ uji k
            by
              inv
                ( compute-elem-at-fixed-point-replace-at-Π-fin-sequence
                  ( succ-ℕ n)
                  ( A)
                  ( j)
                  ( uⱼ)
                  ( replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u)
                  ( k)
                  ( j≠k))
    in
      rec-coproduct
        ( case-i=k)
        ( λ i≠k →
          rec-coproduct
            ( case-j=k)
            ( case-else i≠k)
            ( has-decidable-equality-Fin (n +ℕ 2) j k))
        ( has-decidable-equality-Fin (n +ℕ 2) i k)

  swap-replace-at-Π-fin-sequence :
    (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (uᵢ : A i) (uⱼ : A j)
    (u : Π-fin-sequence (n +ℕ 2) A) →
    replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ
      ( replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ u) ＝
    replace-at-Π-fin-sequence (succ-ℕ n) A j uⱼ
      ( replace-at-Π-fin-sequence (succ-ℕ n) A i uᵢ u)
  swap-replace-at-Π-fin-sequence i j i≠j uᵢ uⱼ u =
    eq-htpy (htpy-swap-replace-at-Π-fin-sequence i j i≠j uᵢ uⱼ u)
```
