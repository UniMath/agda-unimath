# The universal property of flat discrete crisp types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.universal-property-of-flat-discrete-crisp-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.postcomposition-dependent-functions
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import modal-type-theory.action-on-homotopies-flat-modality
open import modal-type-theory.action-on-identifications-crisp-functions
open import modal-type-theory.crisp-function-types
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-discrete-crisp-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

The
{{#concept "universal property" Disambiguation="of flat discrete crisp types" Agda=universal-property-flat-discrete-crisp-type}}
of a [flat discrete crisp type](modal-type-theory.flat-discrete-crisp-types.md)
`A` states that under the [flat modality](modal-type-theory.flat-modality.md)
`♭`, `A` is colocal at the counit of `♭`.

By this we mean that for every [crisp type](modal-type-theory.crisp-types.md)
`B` the map

```text
  coev-flat : ♭ (A → ♭ B) → ♭ (A → B)
```

is an [equivalence](foundation-core.equivalences.md).

## Definitions

### The universal property of flat discrete crisp types

```agda
coev-flat :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2} → ♭ (A → ♭ B) → ♭ (A → B)
coev-flat {A = A} (intro-flat f) = intro-flat (postcomp A counit-flat f)

universal-property-flat-discrete-crisp-type :
  {@♭ l1 : Level} (@♭ A : UU l1) → UUω
universal-property-flat-discrete-crisp-type A =
  {@♭ l : Level} {@♭ B : UU l} → is-equiv (coev-flat {A = A} {B = B})
```

## Properties

### Flat discrete crisp types satisfy the universal property of flat discrete crisp types

This is Corollary 6.15 of {{#cite Shu18}}.

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  abstract
    universal-property-flat-discrete-crisp-type-is-flat-discrete-crisp :
      @♭ is-flat-discrete-crisp A →
      universal-property-flat-discrete-crisp-type A
    universal-property-flat-discrete-crisp-type-is-flat-discrete-crisp
      is-disc-A {B = B} =
      is-equiv-htpy-equiv
        ( ( action-flat-equiv
            ( equiv-precomp (inv-equiv (counit-flat , is-disc-A)) B)) ∘e
          ( equiv-action-flat-map-postcomp-counit-flat) ∘e
          ( action-flat-equiv (equiv-precomp (counit-flat , is-disc-A) (♭ B))))
        ( λ where
          (intro-flat f) →
            crisp-ap
              ( intro-flat)
              ( eq-htpy
                ( λ x →
                  ap
                    ( counit-flat ∘ f)
                    ( inv (is-section-map-inv-is-equiv is-disc-A x)))))
```

## See also

- [The dependent universal property of flat discrete crisp types](modal-type-theory.dependent-universal-property-of-flat-discrete-crisp-types.md)

## References

{{#bibliography}} {{#reference Shu18}}
