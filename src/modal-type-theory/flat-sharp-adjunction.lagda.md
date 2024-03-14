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
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.multivariable-sections
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
open import modal-type-theory.sharp-codiscrete-types
open import modal-type-theory.sharp-modality

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
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
redundancy between the postulated axioms, and they may be subject to change in
the future.

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

### Flat after sharp

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-map-flat-elim-sharp : ♭ (♯ A) → ♭ A
  ap-map-flat-elim-sharp = ap-crisp-map-flat crisp-elim-sharp

  ap-map-flat-unit-sharp : ♭ A → ♭ (♯ A)
  ap-map-flat-unit-sharp = ap-map-flat unit-sharp

  is-section-ap-map-flat-unit-sharp :
    is-section ap-map-flat-elim-sharp ap-map-flat-unit-sharp
  is-section-ap-map-flat-unit-sharp (cons-flat x) =
    crisp-ap cons-flat (compute-crisp-elim-sharp x)

  is-retraction-ap-map-flat-unit-sharp :
    is-retraction ap-map-flat-elim-sharp ap-map-flat-unit-sharp
  is-retraction-ap-map-flat-unit-sharp (cons-flat x) =
    crisp-ap cons-flat (uniqueness-crisp-elim-sharp x)

  is-equiv-ap-map-flat-elim-sharp : is-equiv ap-map-flat-elim-sharp
  pr1 (pr1 is-equiv-ap-map-flat-elim-sharp) = ap-map-flat-unit-sharp
  pr2 (pr1 is-equiv-ap-map-flat-elim-sharp) = is-section-ap-map-flat-unit-sharp
  pr1 (pr2 is-equiv-ap-map-flat-elim-sharp) = ap-map-flat-unit-sharp
  pr2 (pr2 is-equiv-ap-map-flat-elim-sharp) =
    is-retraction-ap-map-flat-unit-sharp

  equiv-ap-map-flat-elim-sharp : ♭ (♯ A) ≃ ♭ A
  pr1 equiv-ap-map-flat-elim-sharp = ap-map-flat-elim-sharp
  pr2 equiv-ap-map-flat-elim-sharp = is-equiv-ap-map-flat-elim-sharp

  is-equiv-ap-map-flat-unit-sharp : is-equiv ap-map-flat-unit-sharp
  pr1 (pr1 is-equiv-ap-map-flat-unit-sharp) = ap-map-flat-elim-sharp
  pr2 (pr1 is-equiv-ap-map-flat-unit-sharp) =
    is-retraction-ap-map-flat-unit-sharp
  pr1 (pr2 is-equiv-ap-map-flat-unit-sharp) = ap-map-flat-elim-sharp
  pr2 (pr2 is-equiv-ap-map-flat-unit-sharp) = is-section-ap-map-flat-unit-sharp

  equiv-ap-map-flat-unit-sharp : ♭ A ≃ ♭ (♯ A)
  pr1 equiv-ap-map-flat-unit-sharp = ap-map-flat-unit-sharp
  pr2 equiv-ap-map-flat-unit-sharp = is-equiv-ap-map-flat-unit-sharp
```

### Sharp after flat

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-sharp-counit-flat : ♯ (♭ A) → ♯ A
  ap-sharp-counit-flat = rec-sharp (unit-sharp ∘ counit-flat)

  ap-sharp-cons-flat : ♯ A → ♯ (♭ A)
  ap-sharp-cons-flat = rec-sharp (crisp-rec-sharp cons-flat)
```

It remains to show that these two are inverses to each other.

### Sharp is uniquely eliminating

This remains to be formalized.

### Crisp identity induction

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  (@♭ C : (@♭ x y : A) → @♭ (x ＝ y) → UU l2)
  (@♭ d : ((@♭ x : A) → C x x refl))
  where

  crisp-ind-Id'' :
    {@♭ x y : A} (@♭ p : x ＝ y) → {!   !} -- C x y p
  crisp-ind-Id'' {x} {y} p =
    (ind-Id
      ( x)
      ( λ y p →
        type-Sharp-Codiscrete-Type
          ( crisp-binary-ind-sharp-codiscrete
            ( λ _ _ → Sharp-Codiscrete-Type l2)
            ( λ _ _ → is-sharp-codiscrete-Sharp-Codiscrete-Type l2)
            ( λ y p → (♯ (C x y p) , is-sharp-codiscrete-sharp (C x y p))) y p))
      {! unit-sharp ?  !}
      {!   !}
      p)
```

## See also

- In [codiscrete types](modal-type-theory.sharp-codiscrete-types.md), we
  postulate that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
