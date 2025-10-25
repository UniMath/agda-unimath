# Prespectra

```agda
module synthetic-homotopy-theory.prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types
```

</details>

## Idea

A **prespectrum** is a [sequence](lists.sequences.md) of
[pointed types](structured-types.pointed-types.md) `Aₙ`
[equipped](foundation.structure.md) with
[pointed maps](structured-types.pointed-maps.md)

```text
  ε : Aₙ →∗ ΩAₙ₊₁
```

for each `n : ℕ`, called the **adjoint structure maps** of the prespectrum.

By the
[loop-suspension adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md),
specifying structure maps `Aₙ →∗ Ω Aₙ₊₁` is
[equivalent](foundation-core.equivalences.md) to specifying their adjoint maps

```text
  ΣAₙ → Aₙ₊₁.
```

## Definition

```agda
Prespectrum : (l : Level) → UU (lsuc l)
Prespectrum l =
  Σ (ℕ → Pointed-Type l) (λ A → (n : ℕ) → A n →∗ Ω (A (succ-ℕ n)))

module _
  {l : Level} (A : Prespectrum l) (n : ℕ)
  where

  pointed-type-Prespectrum : Pointed-Type l
  pointed-type-Prespectrum = pr1 A n

  type-Prespectrum : UU l
  type-Prespectrum = type-Pointed-Type pointed-type-Prespectrum

  point-Prespectrum : type-Prespectrum
  point-Prespectrum = point-Pointed-Type pointed-type-Prespectrum

module _
  {l : Level} (A : Prespectrum l) (n : ℕ)
  where

  pointed-adjoint-structure-map-Prespectrum :
    pointed-type-Prespectrum A n →∗ Ω (pointed-type-Prespectrum A (succ-ℕ n))
  pointed-adjoint-structure-map-Prespectrum = pr2 A n

  adjoint-structure-map-Prespectrum :
    type-Prespectrum A n → type-Ω (pointed-type-Prespectrum A (succ-ℕ n))
  adjoint-structure-map-Prespectrum =
    map-pointed-map pointed-adjoint-structure-map-Prespectrum

  preserves-point-adjoint-structure-map-Prespectrum :
    adjoint-structure-map-Prespectrum (point-Prespectrum A n) ＝
    refl-Ω (pointed-type-Prespectrum A (succ-ℕ n))
  preserves-point-adjoint-structure-map-Prespectrum =
    preserves-point-pointed-map pointed-adjoint-structure-map-Prespectrum
```

### The structure maps of a prespectrum

```agda
module _
  {l : Level} (A : Prespectrum l) (n : ℕ)
  where

  pointed-structure-map-Prespectrum :
    suspension-Pointed-Type (pointed-type-Prespectrum A n) →∗
    pointed-type-Prespectrum A (succ-ℕ n)
  pointed-structure-map-Prespectrum =
    inv-transpose-suspension-loop-adjunction
      ( pointed-type-Prespectrum A n)
      ( pointed-type-Prespectrum A (succ-ℕ n))
      ( pointed-adjoint-structure-map-Prespectrum A n)

  structure-map-Prespectrum :
    suspension (type-Prespectrum A n) → type-Prespectrum A (succ-ℕ n)
  structure-map-Prespectrum = map-pointed-map pointed-structure-map-Prespectrum

  preserves-point-structure-map-Prespectrum :
    structure-map-Prespectrum north-suspension ＝ point-Prespectrum A (succ-ℕ n)
  preserves-point-structure-map-Prespectrum =
    preserves-point-pointed-map pointed-structure-map-Prespectrum
```

## References

{{#bibliography}} {{#reference May99}}
