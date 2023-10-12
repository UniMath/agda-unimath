# Strict maps of prespectra

```agda
module synthetic-homotopy-theory.strict-maps-of-prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.prespectra
```

</details>

## Idea

A **strict-map of presectra** `f : A → B` of degree `r` is a
[sequence](foundation.sequences.md) of maps

```text
  fₙ : Eₙ₊ᵣ → Fₙ
```

such that

```text
        fₙ
  Aₙ₊ᵣ ------> Bₙ
  |            |
  |            |
  |            |
  v            v
  ΩAₙ₊ᵣ₊₁ ---> ΩBₙ₊₁
          Ωfₙ₊₁
```

commute.

## Definition

```agda
coherence-strict-map-Prespectrum :
  {l1 l2 : Level} (n : ℕ) (r : ℕ) (A : Prespectrum l1) (B : Prespectrum l2) →
  ( (n : ℕ) →
    pointed-type-Prespectrum A (n +ℕ r) →∗ pointed-type-Prespectrum B n) →
  UU (l1 ⊔ l2)
coherence-strict-map-Prespectrum n r A B f =
  coherence-square-pointed-maps
    ( f n)
    ( pointed-structure-map-Prespectrum A (n +ℕ r))
    ( pointed-structure-map-Prespectrum B n)
    ( pointed-map-Ω
      ( tr
        ( λ m →
          pointed-map
            ( pointed-type-Prespectrum A m)
            ( pointed-type-Prespectrum B (succ-ℕ n)))
        ( left-successor-law-add-ℕ n r)
        ( f (succ-ℕ n))))

strict-map-Prespectrum :
  {l1 l2 : Level} (r : ℕ) (A : Prespectrum l1) (B : Prespectrum l2) →
  UU (l1 ⊔ l2)
strict-map-Prespectrum r A B =
  Σ ( (n : ℕ) →
      pointed-type-Prespectrum A (n +ℕ r) →∗ pointed-type-Prespectrum B n)
    ( λ f → (n : ℕ) → coherence-strict-map-Prespectrum n r A B f)
```
