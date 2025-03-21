# Functoriality of the sharp modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.functoriality-sharp-modality where
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

open import modal-type-theory.sharp-modality

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-subuniverse-induction
```

</details>

## Idea

The [sharp modality](modal-type-theory.sharp-modality.md) `♯` is functorial.
Given a map `f : A → B`, there is a
[unique](foundation-core.contractible-types.md) map `♯ f : ♯ A → ♯ B` that fits
into a [natural square](foundation-core.commuting-squares-of-maps.md)

```text
         f
    X ------> Y
    |         |
    |         |
    v         v
   ♯ X ----> ♯ Y.
        ♯ f
```

This construction preserves [composition](foundation-core.function-types.md),
[identifications](foundation-core.identity-types.md),
[homotopies](foundation-core.homotopies.md), and
[equivalences](foundation-core.equivalences.md).

## Definitions

### The sharp modality's action on maps

```agda
action-sharp-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → (♯ A → ♯ B)
action-sharp-map f = rec-sharp (unit-sharp ∘ f)
```
