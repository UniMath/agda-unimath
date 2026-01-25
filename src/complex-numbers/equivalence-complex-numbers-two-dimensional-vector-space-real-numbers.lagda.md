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
complex-ℝ² : {l : Level} → ℂ l → type-ℝ-Fin 2 l
complex-ℝ² (a +iℂ b) (inl (inr star)) = a
complex-ℝ² (a +iℂ b) (inr star) = b

inv-complex-ℝ² : {l : Level} → type-ℝ-Fin 2 l → ℂ l
inv-complex-ℝ² v = v (zero-Fin 1) +iℂ v (one-Fin 1)

abstract
  is-section-inv-complex-ℝ² :
    {l : Level} (z : type-ℝ-Fin 2 l) → complex-ℝ² (inv-complex-ℝ² z) ＝ z
  is-section-inv-complex-ℝ² z =
    eq-htpy (λ { (inl (inr star)) → refl ; (inr star) → refl})

  is-retraction-inv-complex-ℝ² :
    {l : Level} (z : ℂ l) → inv-complex-ℝ² (complex-ℝ² z) ＝ z
  is-retraction-inv-complex-ℝ² z = refl

is-equiv-ℂ-ℝ² : (l : Level) → is-equiv (complex-ℝ² {l})
is-equiv-ℂ-ℝ² l =
  is-equiv-is-invertible
    ( inv-complex-ℝ²)
    ( is-section-inv-complex-ℝ²)
    ( is-retraction-inv-complex-ℝ²)

equiv-ℂ-ℝ² : (l : Level) → ℂ l ≃ type-ℝ-Fin 2 l
equiv-ℂ-ℝ² l = (complex-ℝ² , is-equiv-ℂ-ℝ² l)

abstract
  add-complex-ℝ² :
    {l : Level} (z w : ℂ l) →
    complex-ℝ² (z +ℂ w) ＝ add-ℝ-Fin (complex-ℝ² z) (complex-ℝ² w)
  add-complex-ℝ² z w =
    eq-htpy (λ { (inl (inr star)) → refl ; (inr star) → refl})

  neg-complex-ℝ² : {l : Level} (z : ℂ l) →
    complex-ℝ² (neg-ℂ z) ＝ neg-ℝ-Fin (complex-ℝ² z)
  neg-complex-ℝ² z = eq-htpy (λ { (inl (inr star)) → refl ; (inr star) → refl})

  diff-complex-ℝ² :
    {l : Level} (z w : ℂ l) →
    complex-ℝ² (z -ℂ w) ＝ diff-ℝ-Fin (complex-ℝ² z) (complex-ℝ² w)
  diff-complex-ℝ² z w =
    ( add-complex-ℝ² z (neg-ℂ w)) ∙
    ( ap (add-ℝ-Fin (complex-ℝ² z)) (neg-complex-ℝ² w))
```

## See also

- [Distances between complex numbers](complex-numbers.distance-complex-numbers.md)
