# Constant sequences

```agda
module foundation.constant-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pi-decompositions
open import foundation.sequences
open import foundation.universe-levels
```

</details>

## Idea

A [sequence](foundation.sequences.md) `u` is
{{#concept "constant" Disambiguation="sequence" Agda=is-constant-sequence}}
if `u p ＝ u q` for all `p` and `q`.

## Definitions

### Constant sequences

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-constant-sequence : UU l
  is-constant-sequence = (p q : ℕ) → u p ＝ u q
```

### The type of constant sequences in a type

```agda
module _
  {l : Level} (A : UU l)
  where

  constant-sequence : UU l
  constant-sequence = Σ (sequence A) is-constant-sequence
```

### Stationnary values of a sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-stationnary-value-sequence : ℕ → UU l
  is-stationnary-value-sequence n = (u n) ＝ (u (succ-ℕ n))
```

## Properties

### The value of a constant sequence

```agda
module _
  {l : Level} {A : UU l} {u : sequence A} (H : is-constant-sequence u)
  where

  value-constant-sequence : A
  value-constant-sequence = u zero-ℕ

  eq-value-constant-sequence : (n : ℕ) → value-constant-sequence ＝ u n
  eq-value-constant-sequence = H zero-ℕ
```

### Constant sequences are constant

```agda
module _
  {l : Level} {A : UU l} (x : A)
  where

  is-constant-const-sequence : is-constant-sequence (const ℕ x)
  is-constant-const-sequence p q = refl
```

### A sequence is constant if all its terms are equal to some element

```agda
module _
  {l : Level} {A : UU l} (x : A) (u : sequence A)
  where

  is-constant-htpy-constant-sequence :
    (const ℕ x) ~ u → is-constant-sequence u
  is-constant-htpy-constant-sequence H p q = inv (H p) ∙ H q
```

### A sequence is constant if and only if all its values are stationnary

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  is-stationnary-value-is-constant-sequence :
    is-constant-sequence u → Π ℕ (is-stationnary-value-sequence u)
  is-stationnary-value-is-constant-sequence H n = H n (succ-ℕ n)

  is-constant-is-stationnary-value-sequence :
    Π ℕ (is-stationnary-value-sequence u) → is-constant-sequence u
  is-constant-is-stationnary-value-sequence H =
    is-constant-htpy-constant-sequence
      ( u zero-ℕ)
      ( u)
      ( ind-ℕ (refl) (λ n K → K ∙ H n))
```
