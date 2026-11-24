# Submodels of signatures

```agda
module universal-algebra.submodels-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import lists.subtypes-tuples
open import lists.tuples

open import universal-algebra.models-of-signatures
open import universal-algebra.morphisms-of-models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

A [subset](foundation.subtypes.md) of a
[model](universal-algebra.models-of-signatures.md) `M` of a
[signature](universal-algebra.signatures.md) `σ` that is closed under the
operations of `σ` is called a
{{#concept "submodel" Disambiguation="of a model of a signature" Agda=Submodel-Of-Signature}}
of `M` and induces a model of `σ`.

## Definition

```agda
subset-Model-of-Signature :
  {l1 l2 : Level} (l3 : Level) →
  (σ : signature l1) → Model-Of-Signature l2 σ → UU (l2 ⊔ lsuc l3)
subset-Model-of-Signature l3 σ M = subtype l3 (type-Model-Of-Signature σ M)

module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (M : Model-Of-Signature l2 σ)
  (S : subtype l3 (type-Model-Of-Signature σ M))
  where

  is-closed-under-operations-prop-subset-Model-Of-Signature :
    Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-under-operations-prop-subset-Model-Of-Signature =
    Π-Prop
      ( operation-signature σ)
      ( λ op →
        Π-Prop
          ( tuple
            ( type-Model-Of-Signature σ M)
            ( arity-operation-signature σ op))
          ( λ xs →
            all-tuple-subtype S _ xs ⇒
            S ( is-model-set-Model-Of-Signature σ M op xs)))

  is-closed-under-operations-subset-Model-of-Signature :
    UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-operations-subset-Model-of-Signature =
    type-Prop is-closed-under-operations-prop-subset-Model-Of-Signature

Submodel-Of-Signature :
  {l1 l2 : Level} (l3 : Level) →
  (σ : signature l1) → Model-Of-Signature l2 σ → UU (l1 ⊔ l2 ⊔ lsuc l3)
Submodel-Of-Signature l3 σ M =
  type-subtype
    ( is-closed-under-operations-prop-subset-Model-Of-Signature {l3 = l3} σ M)

module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (M : Model-Of-Signature l2 σ)
  ((S , is-closed-S) : Submodel-Of-Signature l3 σ M)
  where

  subset-Submodel-Of-Signature : subset-Model-of-Signature l3 σ M
  subset-Submodel-Of-Signature = S

  is-closed-under-operations-subset-Submodel-Of-Signature :
    is-closed-under-operations-subset-Model-of-Signature
      ( σ)
      ( M)
      ( subset-Submodel-Of-Signature)
  is-closed-under-operations-subset-Submodel-Of-Signature = is-closed-S

  type-Submodel-Of-Signature : UU (l2 ⊔ l3)
  type-Submodel-Of-Signature = type-subtype S

  is-in-Submodel-Of-Signature : type-Model-Of-Signature σ M → UU l3
  is-in-Submodel-Of-Signature = is-in-subtype S

  inclusion-Submodel-Of-Signature :
    type-Submodel-Of-Signature → type-Model-Of-Signature σ M
  inclusion-Submodel-Of-Signature = inclusion-subtype S
```

## Properties

### A submodel of a model of a signature induces a model of the signature

```agda
module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (M : Model-Of-Signature l2 σ)
  ((S , is-closed-S) : Submodel-Of-Signature l3 σ M)
  where

  set-Submodel-Of-Signature : Set (l2 ⊔ l3)
  set-Submodel-Of-Signature =
    set-subset (set-Model-Of-Signature σ M) S

  is-model-set-Submodel-Of-Signature :
    is-model-of-signature σ set-Submodel-Of-Signature
  is-model-set-Submodel-Of-Signature op xs =
    ( is-model-set-Model-Of-Signature σ M
        ( op)
        ( map-inclusion-subtype-tuple S xs) ,
      is-closed-S
        ( op)
        ( map-inclusion-subtype-tuple S xs)
        ( all-tuple-map-inclusion-subtype-tuple S xs))

  model-Submodel-Of-Signature : Model-Of-Signature (l2 ⊔ l3) σ
  model-Submodel-Of-Signature =
    ( set-Submodel-Of-Signature ,
      is-model-set-Submodel-Of-Signature)
```

### The inclusion homomorphism from a submodel of `M` to `M`

```agda
module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (M : Model-Of-Signature l2 σ)
  (SM@(S , is-closed-S) : Submodel-Of-Signature l3 σ M)
  where

  inclusion-hom-Submodel-Of-Signature :
    hom-Model-Of-Signature σ (model-Submodel-Of-Signature σ M SM) M
  inclusion-hom-Submodel-Of-Signature =
    ( inclusion-subtype S ,
      λ op v → refl)
```
