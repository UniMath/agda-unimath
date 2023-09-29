# The sharp modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.sharp-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.locally-small-modal-operators
```

</details>

## Idea

The **sharp modality** is an axiomatized monadic modality we postulate as a
right adjoint to the [flat modality](modal-type-theory.flat-modality.md).

## Definition

```agda
postulate
  ♯ : {l : Level} (A : UU l) → UU l

  unit-♯ : {l : Level} {A : UU l} → A → ♯ A

  ind-♯ :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
    ((x : A) → ♯ (C (unit-♯ x))) →
    ((x : ♯ A) → ♯ (C x))

  compute-ind-♯ :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2)
    (f : (x : A) → ♯ (C (unit-♯ x))) →
    (ind-♯ C f ∘ unit-♯) ~ f

module _
  (l : Level)
  where

  ♯-locally-small-operator-modality : locally-small-operator-modality l l l
  pr1 ♯-locally-small-operator-modality = ♯ {l}
  pr2 ♯-locally-small-operator-modality A = is-locally-small' {l} {♯ A}

  induction-principle-modality-♯ : induction-principle-modality {l} unit-♯
  pr1 (induction-principle-modality-♯ X P) = ind-♯ P
  pr2 (induction-principle-modality-♯ X P) = compute-ind-♯ P
```

### Sharp recursion

```agda
rec-♯ :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) →
    (A → ♯ B) → (♯ A → ♯ B)
rec-♯ B = ind-♯ (λ _ → B)

compute-rec-♯ :
    {l1 l2 : Level} {A : UU l1} (B : UU l2)
    (f : A → ♯ B) →
    (rec-♯ B f ∘ unit-♯) ~ f
compute-rec-♯ B = compute-ind-♯ (λ _ → B)
```

### Action on maps

```agda
ap-♯ : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → (♯ A → ♯ B)
ap-♯ {B = B} f = rec-♯ B (unit-♯ ∘ f)
```

## See also

- In [codiscrete types](modal-type-theory.codiscrete-types.md), we postulate
  that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).
- and in [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md)
  we moreover postulate that the sharp modality is right adjoint to the
  [flat modality](modal-type-theory.flat-modality.md).

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
