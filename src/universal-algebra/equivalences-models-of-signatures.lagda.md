# Equivalences of models of signatures

```agda
module universal-algebra.equivalences-models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.propositions

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.models-of-signatures
open import universal-algebra.morphisms-of-models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

We characterize [equivalences](foundation-core.equivalences.md) of
[models](universal-algebra.models-of-signatures.md) of
[(finitary) signatures](universal-algebra.signatures.md).

## Definitions

### Equivalences of models of signatures

```agda
equiv-Model :
  {l1 l2 l3 : Level} (σ : signature l1)
  (X : Model l2 σ)
  (Y : Model l3 σ) →
  UU (l1 ⊔ l2 ⊔ l3)
equiv-Model σ X Y =
  Σ ( type-Model σ X ≃ type-Model σ Y)
    ( λ e → preserves-operations-Model σ X Y (map-equiv e))

module _
  {l1 l2 l3 : Level} (σ : signature l1)
  (X : Model l2 σ)
  (Y : Model l3 σ)
  (e : equiv-Model σ X Y)
  where

  equiv-type-equiv-Model :
    type-Model σ X ≃ type-Model σ Y
  equiv-type-equiv-Model = pr1 e

  map-type-equiv-Model :
    type-Model σ X → type-Model σ Y
  map-type-equiv-Model = map-equiv equiv-type-equiv-Model

  map-inv-type-equiv-Model :
    type-Model σ Y → type-Model σ X
  map-inv-type-equiv-Model =
    map-inv-equiv equiv-type-equiv-Model

  is-equiv-map-type-equiv-Model :
    is-equiv map-type-equiv-Model
  is-equiv-map-type-equiv-Model =
    is-equiv-map-equiv equiv-type-equiv-Model

  preserves-operations-equiv-Model :
    preserves-operations-Model σ X Y map-type-equiv-Model
  preserves-operations-equiv-Model = pr2 e
```

## Properties

### Characterizing equality of model structures

```agda
module _
  {l1 l2 : Level} (σ : signature l1) {X : UU l2}
  where

  htpy-is-model' : (f g : is-model-type σ X) → UU (l1 ⊔ l2)
  htpy-is-model' f g =
    ( op : operation-signature σ)
    ( v : tuple X (arity-operation-signature σ op)) →
    f op v ＝ g op (map-tuple id v)

  htpy-is-model :
    (f g : is-model-type σ X) → UU (l1 ⊔ l2)
  htpy-is-model f g =
    (op : operation-signature σ) → f op ~ g op

  compute-htpy-is-model :
    (f g : is-model-type σ X) →
    htpy-is-model f g ≃ htpy-is-model' f g
  compute-htpy-is-model f g =
    equiv-Π-equiv-family
      ( λ op →
        equiv-Π-equiv-family
          ( λ v →
            equiv-concat'
              ( f op v)
              ( ap
                ( g op)
                ( preserves-id-map-tuple (arity-operation-signature σ op) v))))

  refl-htpy-is-model' :
    (f : is-model-type σ X) →
    htpy-is-model' f f
  refl-htpy-is-model' f op v =
    ap (f op) (preserves-id-map-tuple (arity-operation-signature σ op) v)

  htpy-eq-is-model' :
    (f g : is-model-type σ X) →
    f ＝ g → htpy-is-model' f g
  htpy-eq-is-model' f .f refl op v =
    ap (f op) (preserves-id-map-tuple (arity-operation-signature σ op) v)

  is-torsorial-htpy-is-model :
    (f : is-model-type σ X) → is-torsorial (htpy-is-model f)
  is-torsorial-htpy-is-model f = is-torsorial-binary-htpy f

  abstract
    is-torsorial-htpy-is-model' :
      (f : is-model-type σ X) → is-torsorial (htpy-is-model' f)
    is-torsorial-htpy-is-model' f =
      is-contr-equiv'
        ( Σ (is-model-type σ X) (htpy-is-model f))
        ( equiv-tot (compute-htpy-is-model f))
        ( is-torsorial-htpy-is-model f)

  abstract
    is-equiv-htpy-eq-is-model' :
      (f g : is-model-type σ X) →
      is-equiv (htpy-eq-is-model' f g)
    is-equiv-htpy-eq-is-model' f =
      fundamental-theorem-id
        ( is-torsorial-htpy-is-model' f)
        ( htpy-eq-is-model' f)
```

### Homotopy of models is a proposition

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (X : Set l2)
  where

  abstract
    is-prop-htpy-is-model' :
      (f g : is-model σ X) → is-prop (htpy-is-model' σ f g)
    is-prop-htpy-is-model' f g =
      is-prop-Π
        ( λ op →
          is-prop-Π
            ( λ v → is-set-type-Set X (f op v) (g op (map-tuple id v))))

  htpy-prop-is-model' :
    (f g : is-model σ X) → Prop (l1 ⊔ l2)
  htpy-prop-is-model' f g =
    ( htpy-is-model' σ f g , is-prop-htpy-is-model' f g)

  abstract
    is-prop-htpy-is-model :
      (f g : is-model σ X) → is-prop (htpy-is-model σ f g)
    is-prop-htpy-is-model f g =
      is-prop-Π (λ op → is-prop-Π (λ v → is-set-type-Set X (f op v) (g op v)))

  htpy-prop-is-model :
    (f g : is-model σ X) → Prop (l1 ⊔ l2)
  htpy-prop-is-model f g =
    ( htpy-is-model σ f g , is-prop-htpy-is-model f g)
```

### The characterization of identities of models

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  id-equiv-Model :
    {l2 : Level} (X : Model l2 σ) → equiv-Model σ X X
  id-equiv-Model X =
    ( id-equiv , preserves-operations-id-Model σ X)

  equiv-eq-Model :
    {l2 : Level} (X Y : Model l2 σ) →
    X ＝ Y → equiv-Model σ X Y
  equiv-eq-Model X .X refl = id-equiv-Model X

  abstract
    is-equiv-equiv-eq-Model :
      {l2 : Level} (X Y : Model l2 σ) →
      is-equiv (equiv-eq-Model X Y)
    is-equiv-equiv-eq-Model (X , X-assign) =
      structure-identity-principle
        ( λ {Y} f (eq , _) →
          preserves-operations-Model σ (X , X-assign) (Y , f) eq)
        ( id-equiv)
        ( preserves-operations-id-Model σ (X , X-assign))
        ( equiv-eq-Model (X , X-assign))
        ( is-equiv-equiv-eq-Set X)
        ( is-equiv-htpy-eq-is-model' σ (λ f z → id (X-assign f z)))

  equiv-equiv-eq-Model :
    {l2 : Level} (X Y : Model l2 σ) →
    (X ＝ Y) ≃ equiv-Model σ X Y
  equiv-equiv-eq-Model X Y =
    ( equiv-eq-Model X Y , is-equiv-equiv-eq-Model X Y)

  eq-equiv-Model :
    {l2 : Level} (X Y : Model l2 σ) →
    equiv-Model σ X Y → X ＝ Y
  eq-equiv-Model X Y = map-inv-equiv (equiv-equiv-eq-Model X Y)
```
