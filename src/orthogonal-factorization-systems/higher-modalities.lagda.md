# Higher modalities

```agda
module orthogonal-factorization-systems.higher-modalities where

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.propositions
open import foundation.sections
open import foundation.small-types
open import foundation.subuniverses
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

## Idea

## Definition

### The universal property of higher modalities

```agda
module _
  {l1 l2 : Level}
  {○ : modal-operator l1 l2}
  (unit-○ : modal-unit ○)
  where

  modal-ind : UU (lsuc l1 ⊔ l2)
  modal-ind =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  modal-rec : UU (lsuc l1 ⊔ l2)
  modal-rec = (X Y : UU l1) → (X → ○ Y) → ○ X → ○ Y

  modal-comp : modal-ind → UU (lsuc l1 ⊔ l2)
  modal-comp ind-○ = 
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  modal-universal-property : UU (lsuc l1 ⊔ l2)
  modal-universal-property =
    Σ modal-ind modal-comp

  modal-rec-modal-ind : modal-ind → modal-rec
  modal-rec-modal-ind ind X Y = ind X (λ _ → Y)
```

### The `is-higher-modality` predicate

```agda
module _
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-modal-operator l1 l2 l1)
  (unit-○ : modal-unit ○)
  where

  is-modal-identity-types : UU (lsuc l1 ⊔ l2)
  is-modal-identity-types =
    (X : UU l1) (x y : ○ X) →
    is-modal (unit-○) (type-is-small (is-locally-small-○ X x y))

  is-higher-modality : UU (lsuc l1 ⊔ l2)
  is-higher-modality =
    modal-universal-property (unit-○) × is-modal-identity-types
```

### Projections for the `is-higher-modality` predicate

```agda
  modal-ind-is-higher-modality : is-higher-modality → modal-ind unit-○
  modal-ind-is-higher-modality = pr1 ∘ pr1

  modal-rec-is-higher-modality : is-higher-modality → modal-rec unit-○
  modal-rec-is-higher-modality =
    modal-rec-modal-ind unit-○ ∘ modal-ind-is-higher-modality

  modal-comp-is-higher-modality :
    (h : is-higher-modality) →
    modal-comp unit-○ (modal-ind-is-higher-modality h)
  modal-comp-is-higher-modality = pr2 ∘ pr1

  is-modal-identity-types-is-higher-modality :
    is-higher-modality → is-modal-identity-types
  is-modal-identity-types-is-higher-modality = pr2
```

### The structure of a higher modality

```agda
higher-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
higher-modality l1 l2 =
  Σ ( locally-small-modal-operator l1 l2 l1)
    ( λ ○ →
      Σ ( modal-unit (pr1 ○))
        ( is-higher-modality ○))
```

### Projections for `higher-modality`

```agda
module _
  {l1 l2 : Level} (h : higher-modality l1 l2)
    where

  locally-small-modal-operator-higher-modality :
    locally-small-modal-operator l1 l2 l1
  locally-small-modal-operator-higher-modality = pr1 h

  modal-operator-higher-modality : modal-operator l1 l2
  modal-operator-higher-modality =
    modal-operator-locally-small-modal-operator
      ( locally-small-modal-operator-higher-modality)

  is-locally-small-modal-operator-higher-modality :
    is-locally-small-modal-operator (modal-operator-higher-modality)
  is-locally-small-modal-operator-higher-modality =
    is-locally-small-locally-small-modal-operator
      ( locally-small-modal-operator-higher-modality)

  modal-unit-higher-modality :
    modal-unit (modal-operator-higher-modality)
  modal-unit-higher-modality = pr1 (pr2 h)

  is-higher-modality-higher-modality :
    is-higher-modality
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
  is-higher-modality-higher-modality = pr2 (pr2 h)

  modal-ind-higher-modality :
    modal-ind (modal-unit-higher-modality)
  modal-ind-higher-modality =
    modal-ind-is-higher-modality
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
      ( is-higher-modality-higher-modality)

  modal-rec-higher-modality :
    modal-rec (modal-unit-higher-modality)
  modal-rec-higher-modality =
    modal-rec-modal-ind
      ( modal-unit-higher-modality)
      ( modal-ind-higher-modality)

  modal-comp-higher-modality :
    modal-comp
      ( modal-unit-higher-modality)
      ( modal-ind-higher-modality)
  modal-comp-higher-modality =
    modal-comp-is-higher-modality
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
      ( is-higher-modality-higher-modality)

  is-modal-identity-types-higher-modality :
    is-modal-identity-types
      ( locally-small-modal-operator-higher-modality)
      ( modal-unit-higher-modality)
  is-modal-identity-types-higher-modality =
    ( is-modal-identity-types-is-higher-modality)
    ( locally-small-modal-operator-higher-modality)
    ( modal-unit-higher-modality)
    ( is-higher-modality-higher-modality)
```

## Properties

### Given a modal recursion principle, the modal operator has an action on maps

```agda
module _
  {l : Level}
  {○ : modal-operator l l} (unit-○ : modal-unit ○)
  where

  map-modal-rec : (rec-○ : modal-rec unit-○) {X Y : UU l} → (X → Y) → ○ X → ○ Y
  map-modal-rec rec-○ {X} {Y} f = rec-○ X Y (unit-○ ∘ f)
```

### `○ X` is modal

```agda
module _
  {l : Level}
  (((○ , is-locally-small-○) , unit-○ , (ind-○ , comp-○) , Id-○) : higher-modality l l)
  (X : UU l)
  where

  map-inv-unit-○ : ○ (○ X) → ○ X
  map-inv-unit-○ = ind-○ (○ X) (λ _ → X) id

  isretr-map-inv-unit-○ : (map-inv-unit-○ ∘ unit-○) ~ id
  isretr-map-inv-unit-○ = comp-○ (○ X) (λ _ → X) id

  ○-issec-map-inv-unit-○ :
    (x' : ○ (○ X)) → ○ (unit-○ (map-inv-unit-○ x') ＝ x')
  ○-issec-map-inv-unit-○ =
    ind-○ (○ X)
      ( λ x'' → unit-○ (map-inv-unit-○ x'') ＝ x'')
      ( unit-○ ∘ (ap unit-○ ∘ isretr-map-inv-unit-○))

  issec-map-inv-unit-○ : (unit-○ ∘ map-inv-unit-○) ~ id
  issec-map-inv-unit-○ x'' =
    map-inv-equiv-is-small
      ( is-locally-small-○ (○ X) (unit-○ (map-inv-unit-○ x'')) x'')
      ( map-inv-is-equiv
        ( Id-○ (○ X) (unit-○ (map-inv-unit-○ x'')) x'')
        ( map-modal-rec unit-○ (modal-rec-modal-ind unit-○ ind-○)
          ( map-equiv-is-small
            ( is-locally-small-○ (○ X) (unit-○ (map-inv-unit-○ x'')) x''))
          ( ○-issec-map-inv-unit-○ x'')))

  is-modal-○ : is-modal unit-○ (○ X)
  pr1 (pr1 is-modal-○) = map-inv-unit-○
  pr2 (pr1 is-modal-○) = issec-map-inv-unit-○
  pr1 (pr2 is-modal-○) = map-inv-unit-○
  pr2 (pr2 is-modal-○) = isretr-map-inv-unit-○
```
