# Models of signatures

```agda
module universal-algebra.models-of-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.transport-along-equivalences
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications

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
  {l1 : Level} (Sg : signature l1)
  where

  is-model : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  is-model X =
    ( f : operation-signature Sg) →
    ( tuple X (arity-operation-signature Sg f) → X)

  is-model-signature : {l2 : Level} → (Set l2) → UU (l1 ⊔ l2)
  is-model-signature X = is-model (type-Set X)

  Model-Signature : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Model-Signature l2 = Σ (Set l2) (λ X → is-model-signature X)

  set-Model-Signature : {l2 : Level} → Model-Signature l2 → Set l2
  set-Model-Signature M = pr1 M

  is-model-set-Model-Signature :
    { l2 : Level} →
    ( M : Model-Signature l2) →
    is-model-signature (set-Model-Signature M)
  is-model-set-Model-Signature M = pr2 M

  type-Model-Signature : {l2 : Level} → Model-Signature l2 → UU l2
  type-Model-Signature M = pr1 (set-Model-Signature M)

  is-set-type-Model-Signature :
    { l2 : Level} →
    ( M : Model-Signature l2) →
    is-set (type-Model-Signature M)
  is-set-type-Model-Signature M = pr2 (set-Model-Signature M)
```

### Characterizing the identity type of models of signatures

```agda
module _
  {l1 : Level} (S : signature l1)
  where

  tr-is-model-signature-equiv-Set :
    {l2 : Level} (X : Model-Signature S l2) (Y : Set l2) →
    is-model-signature S Y →
    equiv-Set (set-Model-Signature S X) Y →
    UU (l1 ⊔ l2)
  tr-is-model-signature-equiv-Set (X , X-assign) Y Y-assign f =
    map-tr-equiv (λ v → (x : pr1 S) → tuple v (pr2 S x) → v) f X-assign ~
    Y-assign

  Eq-Model-Signature : {l2 : Level} (X Y : Model-Signature S l2) → UU (l1 ⊔ l2)
  Eq-Model-Signature (X , X-assign) (Y , Y-assign) =
    Σ
    ( equiv-Set X Y)
    ( tr-is-model-signature-equiv-Set (X , X-assign) Y Y-assign)

  refl-Eq-Model-Signature :
    {l2 : Level} (X : Model-Signature S l2) → Eq-Model-Signature X X
  pr1 (refl-Eq-Model-Signature X) = id-equiv
  pr2 (refl-Eq-Model-Signature (X , X-assign)) f =
    ap
    ( λ z → z X-assign f)
    ( compute-map-tr-equiv-id-equiv (λ v → (x : pr1 S) → tuple v (pr2 S x) → v))

  Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature S l2) → X ＝ Y → Eq-Model-Signature X Y
  Eq-eq-Model-Signature X .X refl = refl-Eq-Model-Signature X

  tr-eq-refl-is-model-signature-equiv-Set :
    {l2 : Level} (X : Set l2) (f g : is-model-signature S X) →
    f ＝ g → tr-is-model-signature-equiv-Set (X , f) X g id-equiv
  tr-eq-refl-is-model-signature-equiv-Set X f .f refl g =
    ap
    ( λ z → z f g)
    ( compute-map-tr-equiv-id-equiv (λ v → (x : pr1 S) → tuple v (pr2 S x) → v))

  is-prop-tr-eq-refl-is-model-signature-equiv-Set :
    {l2 : Level} (X : Set l2) (f g : is-model-signature S X) →
    is-prop (tr-is-model-signature-equiv-Set (X , f) X g id-equiv)
  is-prop-tr-eq-refl-is-model-signature-equiv-Set X f g =
    is-prop-Π (λ h → is-set-hom-Set (tuple-Set X (pr2 S h)) X
      ( map-tr-equiv (λ v → (x : pr1 S) →
        tuple v (pr2 S x) → v) id-equiv f h) (g h))

  tr-eq-refl-is-model-signature-equiv-Set-Prop :
    {l2 : Level} (X : Set l2) (f g : is-model-signature S X) →
    Prop (l1 ⊔ l2)
  pr1 (tr-eq-refl-is-model-signature-equiv-Set-Prop X f g) =
    tr-is-model-signature-equiv-Set (X , f) X g id-equiv
  pr2 (tr-eq-refl-is-model-signature-equiv-Set-Prop X f g) =
    is-prop-tr-eq-refl-is-model-signature-equiv-Set X f g

  is-torsorial-tr-is-model-signature-equiv-Set :
    {l2 : Level} (X : Set l2) (f : is-model-signature S X) →
    is-torsorial (λ z → tr-is-model-signature-equiv-Set (X , f) X z id-equiv)
  pr1 (pr1 (is-torsorial-tr-is-model-signature-equiv-Set X f)) = f
  pr2 (pr1 (is-torsorial-tr-is-model-signature-equiv-Set X f)) =
    tr-eq-refl-is-model-signature-equiv-Set X f f refl
  pr2 (is-torsorial-tr-is-model-signature-equiv-Set X f) (g , p) =
    inv-map-extensionality-type-subtype
    ( tr-eq-refl-is-model-signature-equiv-Set-Prop X f)
    ( tr-eq-refl-is-model-signature-equiv-Set X f f refl)
    ( refl-htpy)
    ( λ h → equiv-funext)
    ( g , p)
    ( inv-htpy (λ h → ap (λ j x → j f h x)
      ( compute-map-tr-equiv-id-equiv
        ( λ v → (x₁ : pr1 S) → tuple v (pr2 S x₁) → v))) ∙h p)

  is-equiv-tr-eq-refl-is-model-signature-equiv-Set :
    {l2 : Level} (X : Set l2) (f g : is-model-signature S X) →
    is-equiv (tr-eq-refl-is-model-signature-equiv-Set X f g)
  is-equiv-tr-eq-refl-is-model-signature-equiv-Set X f =
    fundamental-theorem-id
    ( is-torsorial-tr-is-model-signature-equiv-Set X f)
    ( tr-eq-refl-is-model-signature-equiv-Set X f)

  is-equiv-Eq-eq-Model-Signature :
    {l2 : Level} (X Y : Model-Signature S l2) →
    is-equiv (Eq-eq-Model-Signature X Y)
  is-equiv-Eq-eq-Model-Signature (X , X-assign) =
    structure-identity-principle
    ( λ {Y} → tr-is-model-signature-equiv-Set (X , X-assign) Y)
    ( id-equiv)
    ( pr2 (refl-Eq-Model-Signature (X , X-assign)))
    ( Eq-eq-Model-Signature (X , X-assign))
    ( is-equiv-equiv-eq-Set X)
    ( λ f → is-equiv-tr-eq-refl-is-model-signature-equiv-Set X X-assign f)
```
