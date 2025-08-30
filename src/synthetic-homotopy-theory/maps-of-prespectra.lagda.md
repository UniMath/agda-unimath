# Maps of prespectra

```agda
{-# OPTIONS --guardedness #-}

module synthetic-homotopy-theory.maps-of-prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels

open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.whiskering-pointed-homotopies-composition
open import structured-types.wild-category-of-pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.prespectra
```

</details>

## Idea

A {{#concept "map" Disambiguation="of prespectra" Agda=map-Prespectrum}} of
[prespectra](synthetic-homotopy-theory.prespectra.md) `f : A → B` is a
[sequence](lists.dependent-sequences.md) of
[pointed maps](structured-types.pointed-maps.md)

```text
  fₙ : Aₙ →∗ Bₙ
```

such that the squares

```text
        fₙ
  Aₙ --------> Bₙ
  |            |
  |            |
  |            |
  ∨            ∨
  ΩAₙ₊₁ -----> ΩBₙ₊₁
        Ωfₙ₊₁
```

commute in the
[category of pointed types](structured-types.wild-category-of-pointed-types.md).

## Definitions

### Maps of prespectra

```agda
coherence-map-Prespectrum :
  {l1 l2 : Level} (A : Prespectrum l1) (B : Prespectrum l2) →
  ( (n : ℕ) →
    pointed-type-Prespectrum A n →∗ pointed-type-Prespectrum B n) →
  UU (l1 ⊔ l2)
coherence-map-Prespectrum A B f =
  (n : ℕ) →
  coherence-square-pointed-maps
    ( f n)
    ( pointed-adjoint-structure-map-Prespectrum A n)
    ( pointed-adjoint-structure-map-Prespectrum B n)
    ( pointed-map-Ω (f (succ-ℕ n)))

map-Prespectrum :
  {l1 l2 : Level} (A : Prespectrum l1) (B : Prespectrum l2) →
  UU (l1 ⊔ l2)
map-Prespectrum A B =
  Σ ( (n : ℕ) →
      pointed-type-Prespectrum A n →∗ pointed-type-Prespectrum B n)
    ( λ f → coherence-map-Prespectrum A B f)
```

## Properties

### The identity map on a prespectrum

```agda
module _
  {l : Level} (A : Prespectrum l)
  where

  map-id-map-Prespectrum :
    (n : ℕ) → pointed-type-Prespectrum A n →∗ pointed-type-Prespectrum A n
  map-id-map-Prespectrum _ = id-pointed-map

  coherence-id-map-id-map-Prespectrum :
    coherence-map-Prespectrum A A map-id-map-Prespectrum
  coherence-id-map-id-map-Prespectrum n =
    pointed-homotopy-reasoning
    ( pointed-map-Ω id-pointed-map ∘∗
      pointed-adjoint-structure-map-Prespectrum A n)
    ~∗ id-pointed-map ∘∗ pointed-adjoint-structure-map-Prespectrum A n
      by
        right-whisker-comp-pointed-htpy
          ( pointed-map-Ω id-pointed-map)
          ( id-pointed-map)
          ( preserves-id-pointed-map-Ω)
          ( pointed-adjoint-structure-map-Prespectrum A n)
    ~∗ pointed-adjoint-structure-map-Prespectrum A n
      by
        left-unit-law-comp-pointed-map
          ( pointed-adjoint-structure-map-Prespectrum A n)
    ~∗ pointed-adjoint-structure-map-Prespectrum A n ∘∗ id-pointed-map
      by
        inv-pointed-htpy
          ( right-unit-law-comp-pointed-map
            ( pointed-adjoint-structure-map-Prespectrum A n))

  id-map-Prespectrum : map-Prespectrum A A
  id-map-Prespectrum =
    map-id-map-Prespectrum , coherence-id-map-id-map-Prespectrum
```

## References

{{#bibliography}} {{#reference May99}}
