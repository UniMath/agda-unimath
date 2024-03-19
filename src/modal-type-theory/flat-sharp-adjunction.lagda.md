# The flat-sharp adjunction

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-sharp-adjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
open import modal-type-theory.sharp-codiscrete-types
open import modal-type-theory.sharp-modality
```

</details>

## Idea

We postulate that the [flat modality](modal-type-theory.flat-modality.md) `♭` is
a crisp left adjoint to the
[sharp modality](modal-type-theory.sharp-modality.md) `♯`.

In [The sharp modality](modal-type-theory.sharp-modality.md) we postulated that
`♯` is a [modal operator](orthogonal-factorization-systems.modal-operators.md)
that has a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md).
In the file
[Sharp-Codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
postulated that the [subuniverse](foundation.subuniverses.md) of sharp modal
types has appropriate closure properties. Please note that there is some
redundancy between the postulated axioms, and they are likely to change in the
future.

## Definitions

### Crisp recursion for the sharp modality

```agda
module _
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {C : UU l2}
  (f : (@♭ x : A) → C)
  where

  crisp-rec-sharp : A → ♯ C
  crisp-rec-sharp = crisp-ind-sharp (λ _ → C) f

module _
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {C : UU l2}
  (is-codisc-C : is-sharp-codiscrete C) (f : (@♭ x : A) → C)
  where

  crisp-rec-sharp-codiscrete : A → C
  crisp-rec-sharp-codiscrete =
    crisp-ind-sharp-codiscrete (λ _ → C) (λ _ → is-codisc-C) f

  compute-crisp-rec-sharp-codiscrete :
    (@♭ x : A) → crisp-rec-sharp-codiscrete x ＝ f x
  compute-crisp-rec-sharp-codiscrete =
    compute-crisp-ind-sharp-codiscrete (λ _ → C) (λ _ → is-codisc-C) f
```

## Properties

```agda
crisp-tr-sharp :
  {@♭ l : Level} {@♭ A : UU l} {B : UU l} → (p : A ＝ B) →
  {@♭ x : ♯ A} → unit-sharp (tr (λ X → X) p (crisp-elim-sharp x)) ＝ tr ♯ p x
crisp-tr-sharp refl {x} = uniqueness-crisp-elim-sharp x
```

### Crisp induction on `♯` implies cohesive induction

```agda
ind-crisp-ind-sharp-codiscrete :
  {@♭ l1 : Level} {l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
  ((x : ♯ A) → is-sharp-codiscrete (C x)) →
  ((x : A) → C (unit-sharp x)) →
  (x : ♯ A) → C x
ind-crisp-ind-sharp-codiscrete {A = A} C is-codisc-C f x' =
  crisp-ind-sharp-codiscrete
    ( λ X → (x : ♯ X) (p : X ＝ A) → C (tr ♯ p x))
    ( λ x →
      is-sharp-codiscrete-Π
        ( λ y → is-sharp-codiscrete-Π
          ( λ p → is-codisc-C (tr ♯ p y))))
    ( λ A' →
      crisp-ind-sharp-codiscrete
        ( λ y → (p : A' ＝ A) → C (tr ♯ p y))
        ( λ y → is-sharp-codiscrete-Π (λ p → is-codisc-C (tr ♯ p y)))
        ( λ x p → tr C (crisp-tr-sharp p) (f (tr id p (crisp-elim-sharp x)))))
    ( A)
    ( x')
    ( refl)
```

The accompanying computation principle remains to be fully formalized.

### Flat eats sharp

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  action-flat-map-elim-sharp : ♭ (♯ A) → ♭ A
  action-flat-map-elim-sharp = action-flat-crisp-map crisp-elim-sharp

  action-flat-map-unit-sharp : ♭ A → ♭ (♯ A)
  action-flat-map-unit-sharp = action-flat-map unit-sharp

  is-section-action-flat-map-unit-sharp :
    is-section action-flat-map-elim-sharp action-flat-map-unit-sharp
  is-section-action-flat-map-unit-sharp (intro-flat x) =
    ap-flat (compute-crisp-elim-sharp x)

  is-retraction-action-flat-map-unit-sharp :
    is-retraction action-flat-map-elim-sharp action-flat-map-unit-sharp
  is-retraction-action-flat-map-unit-sharp (intro-flat x) =
    ap-flat (uniqueness-crisp-elim-sharp x)

  is-equiv-action-flat-map-elim-sharp : is-equiv action-flat-map-elim-sharp
  pr1 (pr1 is-equiv-action-flat-map-elim-sharp) = action-flat-map-unit-sharp
  pr2 (pr1 is-equiv-action-flat-map-elim-sharp) =
    is-section-action-flat-map-unit-sharp
  pr1 (pr2 is-equiv-action-flat-map-elim-sharp) = action-flat-map-unit-sharp
  pr2 (pr2 is-equiv-action-flat-map-elim-sharp) =
    is-retraction-action-flat-map-unit-sharp

  equiv-action-flat-map-elim-sharp : ♭ (♯ A) ≃ ♭ A
  pr1 equiv-action-flat-map-elim-sharp = action-flat-map-elim-sharp
  pr2 equiv-action-flat-map-elim-sharp = is-equiv-action-flat-map-elim-sharp

  is-equiv-action-flat-map-unit-sharp : is-equiv action-flat-map-unit-sharp
  pr1 (pr1 is-equiv-action-flat-map-unit-sharp) = action-flat-map-elim-sharp
  pr2 (pr1 is-equiv-action-flat-map-unit-sharp) =
    is-retraction-action-flat-map-unit-sharp
  pr1 (pr2 is-equiv-action-flat-map-unit-sharp) = action-flat-map-elim-sharp
  pr2 (pr2 is-equiv-action-flat-map-unit-sharp) =
    is-section-action-flat-map-unit-sharp

  equiv-action-flat-map-unit-sharp : ♭ A ≃ ♭ (♯ A)
  pr1 equiv-action-flat-map-unit-sharp = action-flat-map-unit-sharp
  pr2 equiv-action-flat-map-unit-sharp = is-equiv-action-flat-map-unit-sharp
```

### Sharp eats flat

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-sharp-counit-flat : ♯ (♭ A) → ♯ A
  ap-sharp-counit-flat = rec-sharp (unit-sharp ∘ counit-flat)

  ap-sharp-intro-flat : ♯ A → ♯ (♭ A)
  ap-sharp-intro-flat = rec-sharp (crisp-rec-sharp intro-flat)
```

It remains to show that these two are inverses to each other.

### Sharp is uniquely eliminating

This remains to be formalized.

## See also

- In [sharp codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
  postulate that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
