# The equivalence between the complex numbers and `ℝ²`

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.equivalence-complex-numbers-two-dimensional-vector-space-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.difference-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.standard-euclidean-vector-spaces

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The [complex numbers](complex-numbers.complex-numbers.md) are
[equivalent](foundation.equivalences.md) to the type of the
[standard Euclidean vector space](linear-algebra.standard-euclidean-vector-spaces.md)
`ℝ²`.

## Definition

```agda
map-ℂ-ℝ² : {l : Level} → ℂ l → type-ℝ^ 2 l
map-ℂ-ℝ² (a +iℂ b) (inl (inr star)) = a
map-ℂ-ℝ² (a +iℂ b) (inr star) = b

map-inv-ℂ-ℝ² : {l : Level} → type-ℝ^ 2 l → ℂ l
map-inv-ℂ-ℝ² v = v (zero-Fin 1) +iℂ v (one-Fin 1)

abstract
  is-section-map-inv-ℂ-ℝ² :
    {l : Level} (z : type-ℝ^ 2 l) → map-ℂ-ℝ² (map-inv-ℂ-ℝ² z) ＝ z
  is-section-map-inv-ℂ-ℝ² z =
    eq-htpy (λ { (inl (inr star)) → refl ; (inr star) → refl})

  is-retraction-map-inv-ℂ-ℝ² :
    {l : Level} (z : ℂ l) → map-inv-ℂ-ℝ² (map-ℂ-ℝ² z) ＝ z
  is-retraction-map-inv-ℂ-ℝ² z = refl

is-equiv-ℂ-ℝ² : (l : Level) → is-equiv (map-ℂ-ℝ² {l})
is-equiv-ℂ-ℝ² l =
  is-equiv-is-invertible
    ( map-inv-ℂ-ℝ²)
    ( is-section-map-inv-ℂ-ℝ²)
    ( is-retraction-map-inv-ℂ-ℝ²)

equiv-ℂ-ℝ² : (l : Level) → ℂ l ≃ type-ℝ^ 2 l
equiv-ℂ-ℝ² l = (map-ℂ-ℝ² , is-equiv-ℂ-ℝ² l)

abstract
  map-add-ℂ-ℝ² :
    {l : Level} (z w : ℂ l) →
    map-ℂ-ℝ² (z +ℂ w) ＝ add-ℝ^ 2 (map-ℂ-ℝ² z) (map-ℂ-ℝ² w)
  map-add-ℂ-ℝ² z w = eq-htpy (λ { (inl (inr star)) → refl ; (inr star) → refl})

  map-neg-ℂ-ℝ² : {l : Level} (z : ℂ l) →
    map-ℂ-ℝ² (neg-ℂ z) ＝ neg-ℝ^ 2 (map-ℂ-ℝ² z)
  map-neg-ℂ-ℝ² z = eq-htpy (λ { (inl (inr star)) → refl ; (inr star) → refl})

  map-diff-ℂ-ℝ² :
    {l : Level} (z w : ℂ l) →
    map-ℂ-ℝ² (z -ℂ w) ＝ diff-ℝ^ 2 (map-ℂ-ℝ² z) (map-ℂ-ℝ² w)
  map-diff-ℂ-ℝ² z w =
    map-add-ℂ-ℝ² z (neg-ℂ w) ∙ ap (add-ℝ^ 2 (map-ℂ-ℝ² z)) (map-neg-ℂ-ℝ² w)
```

## See also

- [Distances between complex numbers](complex-numbers.distance-complex-numbers.md)
