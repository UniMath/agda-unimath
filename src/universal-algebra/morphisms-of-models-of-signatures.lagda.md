# Morphisms of models of signatures

```agda
module universal-algebra.morphisms-of-models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.sets
open import universal-algebra.signatures
open import universal-algebra.models-of-signatures
open import foundation-core.function-types
open import lists.tuples
open import foundation-core.propositions
open import lists.functoriality-tuples
open import foundation-core.identity-types
```

</details>

## Idea

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  preserves-operations-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2)
    (f : hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y)) →
    UU (l1 ⊔ l2)
  preserves-operations-Model-Signature ((X , _) , assign-X) (Y , assign-Y) f =
    ( op : operation-signature σ)
    ( v : tuple X (arity-operation-signature σ op)) →
    f (assign-X op v) ＝ assign-Y op (map-tuple f v)

  is-prop-preserves-operations-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2)
    (f : hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y)) →
    is-prop (preserves-operations-Model-Signature X Y f)
  is-prop-preserves-operations-Model-Signature
    (X , assign-X) ((Y , set-Y) , assign-Y) f =
    is-prop-Π
      ( λ op →
        is-prop-Π
          ( λ v →
            set-Y
              ( f (assign-X op v))
              ( assign-Y op (map-tuple f v))))
```

## Properties

### Characterizing the identity type of morphisms of models of signatures

```agda
  htpy-preserves-operations-Model-Signature :
    {l2 : Level} (X : Set l2) (f g : is-model-signature σ X) → UU (l1 ⊔ l2)
  htpy-preserves-operations-Model-Signature X f g =
    preserves-operations-Model-Signature (X , f) (X , g) id
```
