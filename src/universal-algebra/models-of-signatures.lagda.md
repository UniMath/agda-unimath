# Models of signatures

```agda
module universal-algebra.models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.signatures
```

</details>

## Idea

A
{{#concept "model" Disambiguation="of a finitary signature" Agda=Model-Signature}}
of a [(finitary) signature](universal-algebra.signatures.md) `σ` in a type `A`
is a dependent function that assigns to each function symbol `f` of arity `n`
and `n`-[tuple](lists.tuples.md) of elements of `A` an element of `A`.

## Definitions

### The predicate on a type of being a model

```agda
is-model-type : {l1 l2 : Level} → signature l1 → UU l2 → UU (l1 ⊔ l2)
is-model-type σ X =
  (f : operation-signature σ) →
  tuple X (arity-operation-signature σ f) → X
```

### The predicate on a set of being a model

```agda
is-model : {l1 l2 : Level} → signature l1 → Set l2 → UU (l1 ⊔ l2)
is-model σ X = is-model-type σ (type-Set X)
```

```agda
Model-Signature : {l1 : Level} (l2 : Level) → signature l1 → UU (l1 ⊔ lsuc l2)
Model-Signature l2 σ = Σ (Set l2) (is-model σ)

module _
  {l1 l2 : Level} (σ : signature l1) (X : Model-Signature l2 σ)
  where

  set-Model-Signature : Set l2
  set-Model-Signature = pr1 X

  is-model-set-Model-Signature : is-model σ set-Model-Signature
  is-model-set-Model-Signature = pr2 X

  type-Model-Signature : UU l2
  type-Model-Signature = type-Set set-Model-Signature

  is-set-type-Model-Signature : is-set type-Model-Signature
  is-set-type-Model-Signature = is-set-type-Set set-Model-Signature
```
