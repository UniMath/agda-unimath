# Maps of prespectra

```agda
module synthetic-homotopy-theory.maps-of-prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.prespectra
```

</details>

## Idea

A **map of prespectra** `f : A → B` is a
[sequence](foundation.dependent-sequences.md) of
[pointed maps](structured-types.pointed-maps.md)

```text
  fₙ : Aₙ →∗ Bₙ
```

such that the squares

```text
        fₙ
  Aₙ ────────> Bₙ
  │            │
  │            │
  │            │
  ∨            ∨
  ΩAₙ₊₁ ─────> ΩBₙ₊₁
        Ωfₙ₊₁
```

commute in the category of [pointed types](structured-types.pointed-types.md).

## Definition

```agda
coherence-map-Prespectrum :
  {l1 l2 : Level} (n : ℕ) (A : Prespectrum l1) (B : Prespectrum l2) →
  ( (n : ℕ) →
    pointed-type-Prespectrum A n →∗ pointed-type-Prespectrum B n) →
  UU (l1 ⊔ l2)
coherence-map-Prespectrum n A B f =
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
    ( λ f → (n : ℕ) → coherence-map-Prespectrum n A B f)
```

## References

{{#bibliography}} {{#reference May99}}
