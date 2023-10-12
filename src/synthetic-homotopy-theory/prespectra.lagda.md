# Prespectra

```agda
module synthetic-homotopy-theory.prespectra where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A **prespectrum** is a [sequence](foundation.sequences.md) of
[pointed types](structured-types.pointed-types.md) `Aₙ`
[equipped](foundation.structure.md) with
[pointed maps](structured-types.pointed-maps.md)

```text
  ε : Aₙ →∗ ΩAₙ₊₁
```

for each `n : ℕ`, called the **structure maps** of the prespectrum.

By the
[loop-suspension adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md),
specifying structure maps `Aₙ →∗ ΩAₙ₊₁` is
[equivalent](foundation-core.equivalences.md) to specifying their adjoint maps

```text
  ΣAₙ →∗ Aₙ₊₁.
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

  pointed-structure-map-Prespectrum :
    pointed-type-Prespectrum A n →∗ Ω (pointed-type-Prespectrum A (succ-ℕ n))
  pointed-structure-map-Prespectrum = pr2 A n

  structure-map-Prespectrum :
    type-Prespectrum A n → type-Ω (pointed-type-Prespectrum A (succ-ℕ n))
  structure-map-Prespectrum = map-pointed-map pointed-structure-map-Prespectrum

  preserves-point-structure-map-Prespectrum :
    structure-map-Prespectrum (point-Prespectrum A n) ＝
    refl-Ω (pointed-type-Prespectrum A (succ-ℕ n))
  preserves-point-structure-map-Prespectrum =
    preserves-point-pointed-map pointed-structure-map-Prespectrum
```

## References

- J. P. May, _A Concise Course in Algebraic Topology_, 1999
  ([pdf](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf))
