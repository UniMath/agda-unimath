# The large poset of submodels of signatures

```agda
module universal-algebra.large-poset-submodels-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.large-locale-of-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import lists.subtypes-tuples

open import order-theory.large-posets
open import order-theory.large-subposets

open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.submodels-of-signatures
```

</details>

## Idea

[Submodels](universal-algebra.submodels-of-signatures.md) of
[models](universal-algebra.models-of-signatures.md) of
[signatures](universal-algebra.signatures.md) form a
[large poset](order-theory.large-posets.md) under the containment relation.

## Definition

```agda
module _
  {l1 l2 : Level}
  (σ : signature l1)
  (M : Model-Of-Signature l2 σ)
  where

  is-closed-under-sim-is-closed-under-operations-subset-Model-Of-Signature :
    {l3 l4 : Level}
    (S : subset-Model-of-Signature l3 σ M)
    (T : subset-Model-of-Signature l4 σ M) →
    S ⊆ T → T ⊆ S →
    is-closed-under-operations-subset-Model-of-Signature σ M S →
    is-closed-under-operations-subset-Model-of-Signature σ M T
  is-closed-under-sim-is-closed-under-operations-subset-Model-Of-Signature
    S T S⊆T T⊆S is-closed-S op xs xs⊆T =
    let
      k = arity-operation-signature σ op
    in
      S⊆T
        ( is-model-set-Model-Of-Signature σ M op xs)
        ( is-closed-S op xs (leq-all-tuple-subtype T S T⊆S k xs xs⊆T))

  large-subposet-Submodel-Of-Signature :
    Large-Subposet
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( large-poset-powerset-Large-Locale (type-Model-Of-Signature σ M))
  large-subposet-Submodel-Of-Signature =
    make-Large-Subposet
      ( is-closed-under-operations-prop-subset-Model-Of-Signature σ M)
      ( is-closed-under-sim-is-closed-under-operations-subset-Model-Of-Signature)

  large-poset-Submodel-Of-Signature :
    Large-Poset (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l3 l4 → l2 ⊔ l3 ⊔ l4)
  large-poset-Submodel-Of-Signature =
    large-poset-Large-Subposet
      ( large-poset-powerset-Large-Locale (type-Model-Of-Signature σ M))
      ( large-subposet-Submodel-Of-Signature)

  leq-prop-Submodel-Of-Signature :
    Large-Relation-Prop
      ( λ l3 l4 → l2 ⊔ l3 ⊔ l4)
      ( λ l → Submodel-Of-Signature l σ M)
  leq-prop-Submodel-Of-Signature =
    leq-prop-Large-Poset large-poset-Submodel-Of-Signature

  leq-Submodel-Of-Signature :
    Large-Relation
      ( λ l3 l4 → l2 ⊔ l3 ⊔ l4)
      ( λ l → Submodel-Of-Signature l σ M)
  leq-Submodel-Of-Signature = leq-Large-Poset large-poset-Submodel-Of-Signature
```
