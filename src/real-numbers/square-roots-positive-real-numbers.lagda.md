# Square roots of positive real numbers

```agda
module real-numbers.square-roots-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-positive-real-numbers
```

</details>

## Idea

The
{{#concept "square root" Disambiguation="of a positive real number" Agda=sqrt-ℝ⁺}}
operation on the [positive real numbers](real-numbers.positive-real-numbers.md)
is the inverse to the
[squaring operation](real-numbers.squares-positive-real-numbers.md).

## Definition

```agda
real-sqrt-ℝ⁺ : {l : Level} → ℝ⁺ l → ℝ l
real-sqrt-ℝ⁺ x = real-sqrt-ℝ⁰⁺ (nonnegative-ℝ⁺ x)

sqrt-ℝ⁺ : {l : Level} → ℝ⁺ l → ℝ⁺ l
sqrt-ℝ⁺ x⁺@(x , 0<x) =
  ( real-sqrt-ℝ⁺ x⁺ ,
    is-positive-sqrt-is-positive-ℝ⁰⁺ (nonnegative-ℝ⁺ x⁺) 0<x)
```

## Properties

### The square root operation is the inverse to the squaring operation

```agda
abstract
  is-section-sqrt-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → square-ℝ⁺ (sqrt-ℝ⁺ x) ＝ x
  is-section-sqrt-ℝ⁺ x =
    eq-ℝ⁺ _ _ (ap real-ℝ⁰⁺ (is-section-sqrt-ℝ⁰⁺ (nonnegative-ℝ⁺ x)))

  is-retraction-sqrt-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → sqrt-ℝ⁺ (square-ℝ⁺ x) ＝ x
  is-retraction-sqrt-ℝ⁺ x =
    eq-ℝ⁺ _ _
      ( ( ap real-sqrt-ℝ⁰⁺ (eq-ℝ⁰⁺ _ _ refl)) ∙
        ( ap
          ( real-ℝ⁰⁺)
          ( is-retraction-sqrt-ℝ⁰⁺ (nonnegative-ℝ⁺ x))))

is-equiv-square-ℝ⁺ : {l : Level} → is-equiv (square-ℝ⁺ {l})
is-equiv-square-ℝ⁺ =
  is-equiv-is-invertible
    ( sqrt-ℝ⁺)
    ( is-section-sqrt-ℝ⁺)
    ( is-retraction-sqrt-ℝ⁺)

aut-square-ℝ⁺ : {l : Level} → Aut (ℝ⁺ l)
aut-square-ℝ⁺ = (square-ℝ⁺ , is-equiv-square-ℝ⁺)
```
