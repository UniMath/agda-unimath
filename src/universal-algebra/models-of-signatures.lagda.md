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

A {{#concept "model" Disambiguation="of a signature" Agda=Model-Signature}} of a
[signature](universal-algebra.signatures.md) `σ` in a type `A` is a dependent
function that assigns to each function symbol `f` of arity `n` and
`n`-[tuple](lists.tuples.md) of elements of `A` an element of `A`.

## Definitions

### Models

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  is-model-type : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  is-model-type X =
    (f : operation-signature σ) →
    tuple X (arity-operation-signature σ f) → X

  is-model : {l2 : Level} → Set l2 → UU (l1 ⊔ l2)
  is-model X = is-model-type (type-Set X)

  Model-Signature : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Model-Signature l2 = Σ (Set l2) (is-model)

  set-Model-Signature : {l2 : Level} → Model-Signature l2 → Set l2
  set-Model-Signature = pr1

  is-model-set-Model-Signature :
    {l2 : Level} (M : Model-Signature l2) →
    is-model (set-Model-Signature M)
  is-model-set-Model-Signature = pr2

  type-Model-Signature : {l2 : Level} → Model-Signature l2 → UU l2
  type-Model-Signature M = pr1 (set-Model-Signature M)

  is-set-type-Model-Signature :
    {l2 : Level} (M : Model-Signature l2) →
    is-set (type-Model-Signature M)
  is-set-type-Model-Signature M = pr2 (set-Model-Signature M)
```
