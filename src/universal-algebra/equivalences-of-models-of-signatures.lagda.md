# Equivalences of models of signatures

```agda
module universal-algebra.equivalences-of-models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.type-arithmetic-dependent-pair-types
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
[signatures](universal-algebra.signatures.md).

## Properties

### Characterizing the identity type of model structures over a fixed set

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (X : Set l2)
  where

  htpy-id-Model-Signature :
    (f g : is-model-signature σ X) → UU (l1 ⊔ l2)
  htpy-id-Model-Signature f g =
    preserves-operations-Model-Signature σ (X , f) (X , g) id

  is-prop-htpy-id-Model-Signature :
    (f g : is-model-signature σ X) → is-prop (htpy-id-Model-Signature f g)
  is-prop-htpy-id-Model-Signature f g =
    is-prop-Π
      ( λ op → is-prop-Π
        ( λ v → is-set-type-Set X (f op v) (g op (map-tuple id v))))

  htpy-id-prop-Model-Signature :
    (f g : is-model-signature σ X) → Prop (l1 ⊔ l2)
  pr1 (htpy-id-prop-Model-Signature f g) = htpy-id-Model-Signature f g
  pr2 (htpy-id-prop-Model-Signature f g) = is-prop-htpy-id-Model-Signature f g

  htpy-id-Model-Signature' :
    (f g : is-model-signature σ X) → UU (l1 ⊔ l2)
  htpy-id-Model-Signature' f g = (op : operation-signature σ) → f op ~ g op

  is-prop-htpy-id-Model-Signature' :
    (f g : is-model-signature σ X) → is-prop (htpy-id-Model-Signature' f g)
  is-prop-htpy-id-Model-Signature' f g =
    is-prop-Π (λ op → is-prop-Π (λ v → is-set-type-Set X (f op v) (g op v)))

  htpy-id-prop-Model-Signature' :
    (f g : is-model-signature σ X) → Prop (l1 ⊔ l2)
  pr1 (htpy-id-prop-Model-Signature' f g) = htpy-id-Model-Signature' f g
  pr2 (htpy-id-prop-Model-Signature' f g) = is-prop-htpy-id-Model-Signature' f g

  equiv-htpy-id-htpy-id'-Model-Signature :
    (f g : is-model-signature σ X) →
    htpy-id-Model-Signature' f g ≃ htpy-id-Model-Signature f g
  equiv-htpy-id-htpy-id'-Model-Signature f g =
    equiv-Π-equiv-family
      ( λ op → equiv-Π-equiv-family
        ( λ v → equiv-concat'
          ( f op v)
            ( ap
              ( g op)
              ( preserves-id-map-tuple (arity-operation-signature σ op) v))))

  refl-htpy-id-Model-Signature :
    (f : is-model-signature σ X) →
    htpy-id-Model-Signature f f
  refl-htpy-id-Model-Signature f op v =
    ap (f op) (preserves-id-map-tuple (arity-operation-signature σ op) v)

  htpy-eq-id-Model-Signature :
    (f g : is-model-signature σ X) →
    f ＝ g → htpy-id-Model-Signature f g
  htpy-eq-id-Model-Signature f .f refl op v =
    ap (f op) (preserves-id-map-tuple (arity-operation-signature σ op) v)

  is-torsorial-htpy-id-Model-Signature' :
    (f : is-model-signature σ X) → is-torsorial (htpy-id-Model-Signature' f)
  is-torsorial-htpy-id-Model-Signature' f = is-torsorial-binary-htpy f

  is-torsorial-htpy-id-Model-Signature :
    (f : is-model-signature σ X) → is-torsorial (htpy-id-Model-Signature f)
  is-torsorial-htpy-id-Model-Signature f =
    is-contr-equiv'
      ( Σ (is-model-signature σ X) (htpy-id-Model-Signature' f))
      ( equiv-tot (equiv-htpy-id-htpy-id'-Model-Signature f))
      ( is-torsorial-htpy-id-Model-Signature' f)

  is-equiv-htpy-eq-id-Model-Signature :
    (f g : is-model-signature σ X) →
    is-equiv (htpy-eq-id-Model-Signature f g)
  is-equiv-htpy-eq-id-Model-Signature f =
    fundamental-theorem-id
      ( is-torsorial-htpy-id-Model-Signature f)
      ( htpy-eq-id-Model-Signature f)
```

### The characterization of identities of models

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  Eq-Model-Signature : {l2 : Level} (X Y : Model-Signature σ l2) → UU (l1 ⊔ l2)
  Eq-Model-Signature (X , X-assign) (Y , Y-assign) =
    Σ ( equiv-Set X Y)
      ( λ (f , _) →
        preserves-operations-Model-Signature σ (X , X-assign) (Y , Y-assign) f)

  equiv-Eq-Model-Signature' :
    {l2 : Level} (X Y : Model-Signature σ l2) →
    Eq-Model-Signature X Y ≃
    Σ ( hom-Set (set-Model-Signature σ X) (set-Model-Signature σ Y))
      ( λ f → is-equiv f × preserves-operations-Model-Signature σ X Y f)
  equiv-Eq-Model-Signature' X Y = associative-Σ _ _ _

  refl-Eq-Model-Signature :
    {l2 : Level} (X : Model-Signature σ l2) → Eq-Model-Signature X X
  pr1 (refl-Eq-Model-Signature X) = id-equiv
  pr2 (refl-Eq-Model-Signature X) =
    preserves-operations-id-Model-Signature σ X

  Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) → X ＝ Y → Eq-Model-Signature X Y
  Eq-eq-Model-Signature X .X refl = refl-Eq-Model-Signature X

  is-equiv-Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) →
    is-equiv (Eq-eq-Model-Signature X Y)
  is-equiv-Eq-eq-Model-Signature (X , X-assign) =
    structure-identity-principle
      ( λ {Y} f (eq , _) →
        preserves-operations-Model-Signature σ (X , X-assign) (Y , f) eq)
      ( id-equiv)
      ( preserves-operations-id-Model-Signature σ (X , X-assign))
      ( Eq-eq-Model-Signature (X , X-assign))
      ( is-equiv-equiv-eq-Set X)
      ( is-equiv-htpy-eq-id-Model-Signature σ X (λ f z → id (X-assign f z)))

  equiv-Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) →
    (X ＝ Y) ≃ Eq-Model-Signature X Y
  pr1 (equiv-Eq-eq-Model-Signature X Y) = Eq-eq-Model-Signature X Y
  pr2 (equiv-Eq-eq-Model-Signature X Y) = is-equiv-Eq-eq-Model-Signature X Y

  eq-Eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature σ l2) → Eq-Model-Signature X Y → X ＝ Y
  eq-Eq-Model-Signature X Y = map-inv-equiv (equiv-Eq-eq-Model-Signature X Y)
```
