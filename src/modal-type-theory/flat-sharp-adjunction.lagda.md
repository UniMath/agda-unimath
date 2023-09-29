# The flat-sharp adjunction

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-sharp-adjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import modal-type-theory.codiscrete-types
open import modal-type-theory.crisp-types
open import modal-type-theory.flat-modality
open import modal-type-theory.sharp-modality

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
```

</details>

## Idea

We postulate that the [flat modality](modal-type-theory.flat-modality.md) `♭` is
a crisp left adjoint to the
[sharp modality](modal-type-theory.sharp-modality.md) `♯`.

## Postulates

### Codiscrete types are local at the flat counit

```agda
postulate
  promote :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2) →
    ((x : A) → is-codiscrete (C x)) →
    ((@♭ x : A) → (C x)) → (x : A) → (C x)
  promoteβ :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2)
    (cc : ((x : A) → is-codiscrete (C x))) (f : (@♭ x : A) → (C x)) →
    (@♭ x : A) → (promote C cc f x) ＝ f x
```

### Crisp elimination for the sharp modality

```agda
postulate
  crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A

  compute-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) → (crisp-elim-♯ (unit-♯ x)) ＝ x

  uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : ♯ A) → unit-♯ (crisp-elim-♯ x) ＝ x

  coherence-uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    uniqueness-crisp-elim-♯ (unit-♯ x) ＝ ap unit-♯ (compute-crisp-elim-♯ x)
```

## Properties

### Flat after sharp

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-♭-elim-♯ : ♭ (♯ A) → ♭ A
  ap-♭-elim-♯ = crisp-ap-♭ crisp-elim-♯

  ap-♭-unit-♯ : ♭ A → ♭ (♯ A)
  ap-♭-unit-♯ = ap-♭ unit-♯

  is-section-ap-♭-unit-♯ : ap-♭-elim-♯ ∘ ap-♭-unit-♯ ~ id
  is-section-ap-♭-unit-♯ (con-♭ x) =
    crisp-ap con-♭ (compute-crisp-elim-♯ x)

  is-retraction-ap-♭-unit-♯ : ap-♭-unit-♯ ∘ ap-♭-elim-♯ ~ id
  is-retraction-ap-♭-unit-♯ (con-♭ x) =
    crisp-ap con-♭ (uniqueness-crisp-elim-♯ x)

  is-equiv-ap-♭-elim-♯ : is-equiv ap-♭-elim-♯
  pr1 (pr1 is-equiv-ap-♭-elim-♯) = ap-♭-unit-♯
  pr2 (pr1 is-equiv-ap-♭-elim-♯) = is-section-ap-♭-unit-♯
  pr1 (pr2 is-equiv-ap-♭-elim-♯) = ap-♭-unit-♯
  pr2 (pr2 is-equiv-ap-♭-elim-♯) = is-retraction-ap-♭-unit-♯

  equiv-ap-♭-elim-♯ : ♭ (♯ A) ≃ ♭ A
  pr1 equiv-ap-♭-elim-♯ = ap-♭-elim-♯
  pr2 equiv-ap-♭-elim-♯ = is-equiv-ap-♭-elim-♯

  is-equiv-ap-♭-unit-♯ : is-equiv ap-♭-unit-♯
  pr1 (pr1 is-equiv-ap-♭-unit-♯) = ap-♭-elim-♯
  pr2 (pr1 is-equiv-ap-♭-unit-♯) = is-retraction-ap-♭-unit-♯
  pr1 (pr2 is-equiv-ap-♭-unit-♯) = ap-♭-elim-♯
  pr2 (pr2 is-equiv-ap-♭-unit-♯) = is-section-ap-♭-unit-♯

  equiv-ap-♭-unit-♯ : ♭ A ≃ ♭ (♯ A)
  pr1 equiv-ap-♭-unit-♯ = ap-♭-unit-♯
  pr2 equiv-ap-♭-unit-♯ = is-equiv-ap-♭-unit-♯
```

### Sharp after flat

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  sf1 : ♯ (♭ A) → ♯ A
  sf1 = rec-♯ A (unit-♯ ∘ counit-♭)

  sf2 : ♯ A → ♯ (♭ A)
  sf2 =
    rec-♯
      ( ♭ A)
      ( promote
        ( λ _ → ♯ (♭ A))
        ( λ _ → is-codiscrete-♯ (♭ A))
        ( λ x → unit-♯ (con-♭ x)))

  -- is-section-sf2 : sf1 ∘ sf2 ~ id
  -- is-section-sf2 = {!  ind-♯ ? ?!}
```

## See also

- In [codiscrete types](modal-type-theory.codiscrete-types.md), we postulate
  that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
