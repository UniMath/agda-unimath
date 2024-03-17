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

The
{{#concept "dependent universal property" Disambiguation="of flat discrete crisp types" Agda=universal-property-flat-discrete-crisp-type}}
of a flat discrete crisp type `A` states that for any crisply defined crisp type
family `B : A → 𝒰`, postcomposition by the counit induces an equivalence under
the flat modality

$$
♭ \left(Π_{x :: A} ♭ (B (x))\right) ≃ ♭ \left(Π_{x :: A} B (x)\right)
$$

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

## Properties

### Flat discrete crisp types satisfy the dependent universal property of flat discrete crisp types

This is Theorem 6.16 of {{#cite Shu18}}, and remains to be formalized.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
