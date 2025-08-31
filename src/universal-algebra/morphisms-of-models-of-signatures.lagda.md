# Morphisms of models of signatures

```agda
module universal-algebra.morphisms-of-models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  preserves-operations-Model-Signature :
    {l2 l3 : Level} (X : Model-Signature σ l2) (Y : Model-Signature σ l3)
    (f : hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y)) →
    UU (l1 ⊔ l2 ⊔ l3)
  preserves-operations-Model-Signature ((X , _) , assign-X) (Y , assign-Y) f =
    ( op : operation-signature σ)
    ( v : tuple X (arity-operation-signature σ op)) →
    f (assign-X op v) ＝ assign-Y op (map-tuple f v)

  is-prop-preserves-operations-Model-Signature :
    {l2 l3 : Level} (X : Model-Signature σ l2) (Y : Model-Signature σ l3)
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

  prop-preserves-operations-Model-Signature :
    {l2 l3 : Level} (X : Model-Signature σ l2) (Y : Model-Signature σ l3)
    (f : hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y)) →
    Prop (l1 ⊔ l2 ⊔ l3)
  pr1 (prop-preserves-operations-Model-Signature X Y f) =
    preserves-operations-Model-Signature X Y f
  pr2 (prop-preserves-operations-Model-Signature X Y f) =
    is-prop-preserves-operations-Model-Signature X Y f

  hom-Model-Signature :
    {l2 l3 : Level} (X : Model-Signature σ l2) (Y : Model-Signature σ l3) →
    UU (l1 ⊔ l2 ⊔ l3)
  hom-Model-Signature X Y =
    Σ
      ( hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y))
      ( preserves-operations-Model-Signature X Y)

  map-hom-Model-Signature :
    {l2 l3 : Level} (X : Model-Signature σ l2) (Y : Model-Signature σ l3) →
    hom-Model-Signature X Y →
    hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y)
  map-hom-Model-Signature X Y (f , _) = f

  preserves-operations-hom-Model-Signature :
    {l2 l3 : Level} {X : Model-Signature σ l2} {Y : Model-Signature σ l3} →
    (f : hom-Model-Signature X Y) →
    preserves-operations-Model-Signature X Y (map-hom-Model-Signature X Y f)
  preserves-operations-hom-Model-Signature (f , p) = p
```

## Properties

### The identity morphism of a model

```agda
preserves-operations-id-Model-Signature :
  {l1 l2 : Level} (σ : signature l1) (X : Model-Signature σ l2) →
  preserves-operations-Model-Signature σ X X id
preserves-operations-id-Model-Signature σ ((X , _) , assign-X) op v =
  ap
    ( assign-X op)
    ( preserves-id-map-tuple (arity-operation-signature σ op) v)

id-hom-Model-Signature :
  {l1 l2 : Level} (σ : signature l1) (X : Model-Signature σ l2) →
  hom-Model-Signature σ X X
pr1 (id-hom-Model-Signature σ X) = id
pr2 (id-hom-Model-Signature σ X) = preserves-operations-id-Model-Signature σ X
```

### Characterizing the identity type of morphisms of model structures

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X : Model-Signature σ l2) (Y : Model-Signature σ l3)
  where

  htpy-hom-Model-Signature : (f g : hom-Model-Signature σ X Y) → UU (l2 ⊔ l3)
  htpy-hom-Model-Signature (f , _) (g , _) =
    ( x : type-Model-Signature σ X) → f x ＝ g x

  htpy-eq-hom-Model-Signature :
    ( f g : hom-Model-Signature σ X Y) →
    f ＝ g → htpy-hom-Model-Signature f g
  htpy-eq-hom-Model-Signature f .f refl = refl-htpy

  is-equiv-htpy-eq-hom-Model-Signature :
    (f g : hom-Model-Signature σ X Y) →
    is-equiv (htpy-eq-hom-Model-Signature f g)
  is-equiv-htpy-eq-hom-Model-Signature (f , hom-f) =
    subtype-identity-principle
      ( is-prop-preserves-operations-Model-Signature σ X Y)
      ( hom-f)
      ( refl-htpy)
      ( htpy-eq-hom-Model-Signature (f , hom-f))
      ( funext f)
```
