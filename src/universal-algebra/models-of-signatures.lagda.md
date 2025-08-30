# Models of signatures

```agda
{-# OPTIONS --lossy-unification #-}

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

A model of a signature `Sig` in a type `A` is a dependent function that assigns
to each function symbol `f` of arity `n` and `n`-tuple of elements of `A` an
element of `A`.

## Definitions

### Models

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  is-model : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  is-model X =
    ( f : operation-signature σ) →
    ( tuple X (arity-operation-signature σ f) → X)

  is-model-signature : {l2 : Level} → (Set l2) → UU (l1 ⊔ l2)
  is-model-signature X = is-model (type-Set X)

  Model-Signature : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Model-Signature l2 = Σ (Set l2) (λ X → is-model-signature X)

  set-Model-Signature : {l2 : Level} → Model-Signature l2 → Set l2
  set-Model-Signature M = pr1 M

  is-model-set-Model-Signature :
    {l2 : Level} →
    (M : Model-Signature l2) →
    is-model-signature (set-Model-Signature M)
  is-model-set-Model-Signature M = pr2 M

  type-Model-Signature : {l2 : Level} → Model-Signature l2 → UU l2
  type-Model-Signature M = pr1 (set-Model-Signature M)

  is-set-type-Model-Signature :
    {l2 : Level} →
    (M : Model-Signature l2) →
    is-set (type-Model-Signature M)
  is-set-type-Model-Signature M = pr2 (set-Model-Signature M)
```

### Characterizing the identity type of models of signatures

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
    ((X , set-X) , assign-X) ((Y , set-Y) , assign-Y) f =
    is-prop-Π
      ( λ op →
        is-prop-Π
          ( λ v →
            set-Y
              ( f (assign-X op v))
              ( assign-Y op (map-tuple f v))))

  Eq-Model-Signature : {l2 : Level} (X Y : Model-Signature σ l2) → UU (l1 ⊔ l2)
  Eq-Model-Signature (X , X-assign) (Y , Y-assign) =
    Σ ( equiv-Set X Y)
      ( λ (f , _) →
        preserves-operations-Model-Signature (X , X-assign) (Y , Y-assign) f)

  equiv-Eq-Model-Signature' :
    {l2 : Level} (X Y : Model-Signature σ l2) →
    Eq-Model-Signature X Y ≃
    Σ ( hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y))
      ( λ f → is-equiv f × preserves-operations-Model-Signature X Y f)
  pr1 (equiv-Eq-Model-Signature' X Y) ((f , eq) , p) = (f , eq , p)
  pr1 (pr1 (pr2 (equiv-Eq-Model-Signature' X Y))) (f , eq , p) = ((f , eq) , p)
  pr2 (pr1 (pr2 (equiv-Eq-Model-Signature' X Y))) _ = refl
  pr1 (pr2 (pr2 (equiv-Eq-Model-Signature' X Y))) (f , eq , p) = ((f , eq) , p)
  pr2 (pr2 (pr2 (equiv-Eq-Model-Signature' X Y))) _ = refl

  preserves-operations-id-Model-Signature :
    {l2 : Level} (X : Model-Signature σ l2) →
    preserves-operations-Model-Signature X X id
  preserves-operations-id-Model-Signature ((X , _) , assign-X) op v =
    ap
      ( assign-X op)
      ( preserves-id-map-tuple (arity-operation-signature σ op) v)

  refl-Eq-Model-Signature :
    {l2 : Level} (X : Model-Signature σ l2) → Eq-Model-Signature X X
  pr1 (refl-Eq-Model-Signature X) = id-equiv
  pr2 (refl-Eq-Model-Signature X) =
    preserves-operations-id-Model-Signature X

  htpy-preserves-operations-Model-Signature :
    {l2 : Level} (X : Set l2) (f g : is-model-signature σ X) → UU (l1 ⊔ l2)
  htpy-preserves-operations-Model-Signature X f g =
    preserves-operations-Model-Signature (X , f) (X , g) id

  htpy-eq-preserves-operations-Model-Signature :
    {l2 : Level} (X : Set l2) (f g : is-model-signature σ X) →
    f ＝ g → htpy-preserves-operations-Model-Signature X f g
  htpy-eq-preserves-operations-Model-Signature (X , _) f .f refl op v =
    ap (f op) (preserves-id-map-tuple (arity-operation-signature σ op) v)

  eq-htpy-preserves-operations-Model-Signature :
    {l2 : Level} (X : Set l2) (f g : is-model-signature σ X) →
    htpy-preserves-operations-Model-Signature X f g → f ＝ g
  eq-htpy-preserves-operations-Model-Signature (X , _) f g p =
    eq-htpy
    ( λ op →
      eq-htpy
        ( λ v →
          ( p op v) ∙
          ( inv
            ( ap
              ( g op)
              ( preserves-id-map-tuple (arity-operation-signature σ op) v)))))

  is-equiv-htpy-eq-preserves-operations-Model-Signature :
    {l2 : Level} (X : Set l2) (f g : is-model-signature σ X) →
    is-equiv (htpy-eq-preserves-operations-Model-Signature X f g)
  pr1 (pr1 (is-equiv-htpy-eq-preserves-operations-Model-Signature X f g)) =
    eq-htpy-preserves-operations-Model-Signature X f g
  pr2 (pr1 (is-equiv-htpy-eq-preserves-operations-Model-Signature X f g)) p =
    eq-htpy
      ( λ op →
        eq-htpy
          ( λ v →
            pr1
              ( is-set-type-Set X
                ( f op v)
                ( g op (map-tuple id v))
              ( htpy-eq-preserves-operations-Model-Signature X f g
                ( eq-htpy-preserves-operations-Model-Signature X f g p)
              ( op)
              ( v))
          ( p op v))))
  pr1 (pr2 (is-equiv-htpy-eq-preserves-operations-Model-Signature X f g)) =
    eq-htpy-preserves-operations-Model-Signature X f g
  pr2 (pr2 (is-equiv-htpy-eq-preserves-operations-Model-Signature X f .f))
    refl =
      is-set-has-uip
        ( is-set-Π (λ op → is-set-function-type (is-set-type-Set X)))
        ( f)
        ( f)
        ( eq-htpy-preserves-operations-Model-Signature X f f
          ( htpy-eq-preserves-operations-Model-Signature X f f refl))
        ( refl)

  Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) → X ＝ Y → Eq-Model-Signature X Y
  Eq-eq-Model-Signature X .X refl = refl-Eq-Model-Signature X

  is-equiv-Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) →
    is-equiv (Eq-eq-Model-Signature X Y)
  is-equiv-Eq-eq-Model-Signature (X , X-assign) =
    structure-identity-principle
      ( λ {Y} f (eq , _) →
        preserves-operations-Model-Signature (X , X-assign) (Y , f) eq)
      ( id-equiv)
      ( preserves-operations-id-Model-Signature (X , X-assign))
      ( Eq-eq-Model-Signature (X , X-assign))
      ( is-equiv-equiv-eq-Set X)
      ( is-equiv-htpy-eq-preserves-operations-Model-Signature X X-assign)

  equiv-Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) →
    (X ＝ Y) ≃ Eq-Model-Signature X Y
  pr1 (equiv-Eq-eq-Model-Signature X Y) = Eq-eq-Model-Signature X Y
  pr2 (equiv-Eq-eq-Model-Signature X Y) = is-equiv-Eq-eq-Model-Signature X Y

  eq-Eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) → Eq-Model-Signature X Y → X ＝ Y
  eq-Eq-Model-Signature X Y = map-inv-equiv (equiv-Eq-eq-Model-Signature X Y)
```
