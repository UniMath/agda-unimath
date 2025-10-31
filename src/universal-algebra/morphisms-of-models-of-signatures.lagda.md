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

A
{{#concept "morphism" Disambiguation="of models over a signature" Agda=hom-Model-Signature}}
of `σ`-[models](universal-algebra.models-of-signatures.md) `A` and `B` is a
function `f : A → B` between their underlying [sets](foundation-core.sets.md)
that preserves the operations of `σ`, in the sense that for `op ∈ σ` an abstract
operation with arity `n : ℕ`, and `assign-A` and `assign-B` the semantics of `σ`
in `A` and `B` respectively, and for a `v : tuple A n`, we have

```text
  f (assign-A op v) = assign-B op (f v).
```

## Definitions

### The predicate on maps of models of preserving operations

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X'@((X , is-set-X) , assign-X) : Model-Signature σ l2)
  (Y'@((Y , is-set-Y) , assign-Y) : Model-Signature σ l3)
  (f : type-Model-Signature σ X' → type-Model-Signature σ Y')
  where

  preserves-operations-Model-Signature :
    UU (l1 ⊔ l2 ⊔ l3)
  preserves-operations-Model-Signature =
    ( op : operation-signature σ)
    ( v : tuple X (arity-operation-signature σ op)) →
    f (assign-X op v) ＝ assign-Y op (map-tuple f v)

  abstract
    is-prop-preserves-operations-Model-Signature :
      is-prop preserves-operations-Model-Signature
    is-prop-preserves-operations-Model-Signature =
      is-prop-Π
        ( λ op →
          is-prop-Π
            ( λ v →
              is-set-Y
                ( f (assign-X op v))
                ( assign-Y op (map-tuple f v))))

  prop-preserves-operations-Model-Signature : Prop (l1 ⊔ l2 ⊔ l3)
  prop-preserves-operations-Model-Signature =
    ( preserves-operations-Model-Signature ,
      is-prop-preserves-operations-Model-Signature)
```

### The type of morphisms of models of a signature

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X : Model-Signature σ l2) (Y : Model-Signature σ l3)
  where

  hom-Model-Signature : UU (l1 ⊔ l2 ⊔ l3)
  hom-Model-Signature =
    Σ ( type-Model-Signature σ X → type-Model-Signature σ Y)
      ( preserves-operations-Model-Signature σ X Y)

  map-hom-Model-Signature :
    hom-Model-Signature →
    type-Model-Signature σ X → type-Model-Signature σ Y
  map-hom-Model-Signature (f , _) = f

  preserves-operations-hom-Model-Signature :
    (f : hom-Model-Signature) →
    preserves-operations-Model-Signature σ X Y (map-hom-Model-Signature f)
  preserves-operations-hom-Model-Signature (f , p) = p
```

## Properties

### The identity morphism of a model

```agda
module _
  {l1 l2 : Level} (σ : signature l1)
  (X'@((X , _) , assign-X) : Model-Signature σ l2)
  where

  preserves-operations-id-Model-Signature :
    preserves-operations-Model-Signature σ X' X' id
  preserves-operations-id-Model-Signature op v =
    ap
      ( assign-X op)
      ( preserves-id-map-tuple (arity-operation-signature σ op) v)

  id-hom-Model-Signature : hom-Model-Signature σ X' X'
  id-hom-Model-Signature = (id , preserves-operations-id-Model-Signature)
```

### Characterizing the identity type of morphisms of models

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X : Model-Signature σ l2) (Y : Model-Signature σ l3)
  where

  htpy-hom-Model-Signature :
    (f g : hom-Model-Signature σ X Y) → UU (l2 ⊔ l3)
  htpy-hom-Model-Signature (f , _) (g , _) =
    ( x : type-Model-Signature σ X) → f x ＝ g x

  htpy-eq-hom-Model-Signature :
    (f g : hom-Model-Signature σ X Y) →
    f ＝ g → htpy-hom-Model-Signature f g
  htpy-eq-hom-Model-Signature f .f refl = refl-htpy

  abstract
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
