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
```

## Idea

## Definition

```agda
module _
  {l1 l2 : Level}
  ((○ , is-locally-small-○) : locally-small-modal-operator l1 l2 l1)
  (unit-○ : modal-unit ○)
  where

  modality-induction-principle : UU (lsuc l1 ⊔ l2)
  modality-induction-principle =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  modality-recursion-principle : UU (lsuc l1 ⊔ l2)
  modality-recursion-principle =
    (X : UU l1) (Y : UU l1) → (X → ○ Y) → ○ X → ○ Y

  modality-computation-principle :
    modality-induction-principle → UU (lsuc l1 ⊔ l2)
  modality-computation-principle ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ X P f (unit-○ x) ＝ f x

  is-modal-identity-types : UU (lsuc l1 ⊔ l2)
  is-modal-identity-types =
    (X : UU l1) (x y : ○ X) →
    is-modal (unit-○) (type-is-small (is-locally-small-○ X x y))

  is-higher-modality : UU (lsuc l1 ⊔ l2)
  is-higher-modality =
    is-modal-identity-types ×
      Σ ( modality-induction-principle)
        ( modality-computation-principle)

  is-modal-identity-types-is-higher-modality :
    is-higher-modality → is-modal-identity-types
  is-modal-identity-types-is-higher-modality = pr1

  induction-principle-is-higher-modality :
    is-higher-modality → modality-induction-principle
  induction-principle-is-higher-modality = pr1 ∘ pr2

  computation-principle-is-higher-modality :
    (h : is-higher-modality) →
    modality-computation-principle (induction-principle-is-higher-modality h)
  computation-principle-is-higher-modality = pr2 ∘ pr2

higher-modality : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
higher-modality l1 l2 =
  Σ ( locally-small-modal-operator l1 l2 l1)
    ( λ ○ →
      Σ ( modal-unit (pr1 ○))
        ( is-higher-modality ○))

module _
  {l1 l2 : Level} (h : higher-modality l1 l2)
    where

  locally-small-modal-operator-higher-modality :
    locally-small-modal-operator l1 l2 l1
  locally-small-modal-operator-higher-modality = pr1 h

  modal-operator-higher-modality : modal-operator l1 l2
  modal-operator-higher-modality =
    modal-operator-locally-small-modal-operator
      locally-small-modal-operator-higher-modality

  is-locally-small-modal-operator-higher-modality :
    is-locally-small-modal-operator (modal-operator-higher-modality)
  is-locally-small-modal-operator-higher-modality =
    is-locally-small-locally-small-modal-operator
      locally-small-modal-operator-higher-modality

  modal-unit-higher-modality : modal-unit modal-operator-higher-modality
  modal-unit-higher-modality = pr1 (pr2 h)

  is-higher-modality-higher-modality :
    is-higher-modality
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
  is-higher-modality-higher-modality = pr2 (pr2 h)

  is-modal-identity-types-higher-modality :
    is-modal-identity-types
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
  is-modal-identity-types-higher-modality =
    is-modal-identity-types-is-higher-modality
    locally-small-modal-operator-higher-modality
    modal-unit-higher-modality
    is-higher-modality-higher-modality

  induction-principle-higher-modality :
    modality-induction-principle
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
  induction-principle-higher-modality =
    induction-principle-is-higher-modality
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
      is-higher-modality-higher-modality

  computation-principle-higher-modality :
      modality-computation-principle
        locally-small-modal-operator-higher-modality
        modal-unit-higher-modality
        induction-principle-higher-modality
  computation-principle-higher-modality =
    computation-principle-is-higher-modality
      locally-small-modal-operator-higher-modality
      modal-unit-higher-modality
      is-higher-modality-higher-modality
```

## Properties

### For higher modalities the modal operator of is a functor

```agda
module _
  {l : Level} (h : higher-modality l l)
  where

  private
    ○ = modal-operator-higher-modality h
    unit-○ = modal-unit-higher-modality h
    ind-○ = induction-principle-higher-modality h

  map-○ : {X Y : UU l} → (X → Y) → ○ X → ○ Y
  map-○ {X} {Y} f = ind-○ X (λ _ → Y) (unit-○ ∘ f)
```

### For higher modalities `○ X` is modal

```agda
module _
  {l : Level}
  (h : higher-modality l l)
  (X : UU l)
  where

  private
    ○ = modal-operator-higher-modality h
    is-locally-small-○ = is-locally-small-modal-operator-higher-modality h
    unit-○ = modal-unit-higher-modality h
    Id-○ = is-modal-identity-types-higher-modality h
    ind-○ = induction-principle-higher-modality h
    comp-○ = computation-principle-higher-modality h

  map-inv-unit-○ : ○ (○ X) → ○ X
  map-inv-unit-○ = ind-○ (○ X) (λ _ → X) id

  isretr-map-inv-unit-○ : (map-inv-unit-○ ∘ unit-○) ~ id
  isretr-map-inv-unit-○ = comp-○ (○ X) (λ _ → X) id

  ○-issec-map-inv-unit-○ : (x' : ○ (○ X)) → ○ (unit-○ (map-inv-unit-○ x') ＝ x')
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
        ( map-○ h
          ( map-equiv-is-small
            ( is-locally-small-○ (○ X) (unit-○ (map-inv-unit-○ x'')) x''))
          ( ○-issec-map-inv-unit-○ x'')))
```
