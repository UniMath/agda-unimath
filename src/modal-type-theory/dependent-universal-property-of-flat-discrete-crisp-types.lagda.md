# Dependent universal property of flat discrete crisp types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.dependent-universal-property-of-flat-discrete-crisp-types where
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

A crisp type is said to be
{{$concept "flat discrete" Disambiguation="crisp type" Agda=is-flat-discrete-crisp}}
if it is [flat](modal-type-theory.flat-modality.md) modal. I.e. if the flat
counit is an [equivalence](foundation-core.equivalences.md) at that type.

**Terminology:** In _Brouwer's fixed-point theorem in real-cohesive homotopy
type theory_, this is called a _crisply discrete_ type.

The
{{#concept "universal property" Disambiguation="of flat discrete crisp types" Agda=universal-property-flat-discrete-crisp-type}}
of flat discrete crisp types states that

## Definitions

### The dependent universal property of flat discrete crisp types

```agda
dependent-coev-flat :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2} →
  ♭ ((@♭ x : A) → ♭ (B x)) → ♭ ((@♭ x : A) → B x)
dependent-coev-flat (cons-flat f) = cons-flat (λ x → counit-flat (f x))

dependent-universal-property-flat-discrete-crisp-type :
  {@♭ l1 : Level} (@♭ A : UU l1) → UUω
dependent-universal-property-flat-discrete-crisp-type A =
  {@♭ l : Level} {@♭ B : @♭ A → UU l} → is-equiv (dependent-coev-flat {B = B})
```

<!-- TODO: is B : @♭ A → UU l correct? -->

## Properties

### Flat discrete crisp types satisfy the dependent universal property of flat discrete crisp types

This is Corollary 6.15 of {{#cite Shu18}}.

```agda
module _
  {@♭ l1 : Level} {@♭ A : UU l1} (@♭ is-disc-A : is-flat-discrete-crisp A)
  where

  abstract
    dependent-universal-property-flat-discrete-crisp-type-is-flat-discrete-crisp :
      dependent-universal-property-flat-discrete-crisp-type A
    dependent-universal-property-flat-discrete-crisp-type-is-flat-discrete-crisp
      {B = B} =
      is-equiv-htpy-equiv
        {!   !}
        {!   !}
```

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
