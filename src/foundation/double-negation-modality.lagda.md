# The double negation modality

```agda
module foundation.double-negation-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.function-types
open import foundation.irrefutable-propositions
open import foundation.negation
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.transport-along-identifications

open import logic.double-negation-elimination
open import logic.oracle-modalities
open import logic.oracle-reflections

open import orthogonal-factorization-systems.continuation-modalities
open import orthogonal-factorization-systems.large-lawvere-tierney-topologies
open import orthogonal-factorization-systems.lawvere-tierney-topologies
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

The [double negation](foundation.double-negation.md) operation `¬¬` is a
[modality](orthogonal-factorization-systems.higher-modalities.md).

## Definition

### The double negation modality

```agda
operator-double-negation-modality :
  (l : Level) → operator-modality l l
operator-double-negation-modality _ = ¬¬_

unit-double-negation-modality :
  {l : Level} → unit-modality (operator-double-negation-modality l)
unit-double-negation-modality = intro-double-negation
```

## Properties

### The double negation modality is a uniquely eliminating modality

The double negation modality is an instance of a
[continuation modality](orthogonal-factorization-systems.continuation-modalities.md).

```agda
is-uniquely-eliminating-modality-double-negation-modality :
  {l : Level} →
  is-uniquely-eliminating-modality (unit-double-negation-modality {l})
is-uniquely-eliminating-modality-double-negation-modality {l} =
  is-uniquely-eliminating-modality-continuation-modality l empty-Prop
```

### The double negation modality defines a Lawvere–Tierney topology

```agda
is-large-lawvere-tierney-topology-double-negation :
  is-large-lawvere-tierney-topology double-negation-Prop
is-large-lawvere-tierney-topology-double-negation =
  λ where
  .is-idempotent-is-large-lawvere-tierney-topology P →
    ( double-negation-elim-neg (¬ type-Prop P) , intro-double-negation)
  .preserves-unit-is-large-lawvere-tierney-topology →
    preserves-unit-continuation-modality'
  .preserves-conjunction-is-large-lawvere-tierney-topology P Q →
    distributive-product-continuation-modality'

large-lawvere-tierney-topology-double-negation :
  large-lawvere-tierney-topology (λ l → l)
large-lawvere-tierney-topology-double-negation =
  λ where
  .operator-large-lawvere-tierney-topology →
    double-negation-Prop
  .is-large-lawvere-tierney-topology-large-lawvere-tierney-topology →
    is-large-lawvere-tierney-topology-double-negation
```

### Double negation is the excluded middle oracle modality

```agda
excluded-middle-oracle :
  {l : Level} → Prop l → Prop l
excluded-middle-oracle = is-decidable-Prop

module _
  {l1 : Level} (l2 : Level) {X : UU l1}
  where

  ask-double-negation-excluded-middle-oracle :
    (P : Prop (l1 ⊔ l2)) → (is-decidable-type-Prop P → ¬¬ X) → ¬¬ X
  ask-double-negation-excluded-middle-oracle P f nx =
    is-irrefutable-is-decidable-Prop P (λ d → f d nx)

  oracle-algebra-double-negation-excluded-middle-oracle :
    oracle-algebra excluded-middle-oracle X (double-negation-type-Prop X)
  oracle-algebra-double-negation-excluded-middle-oracle =
    ( intro-double-negation , ask-double-negation-excluded-middle-oracle)

module _
  {l1 l2 : Level}
  {X : UU l1}
  (Q : ¬¬ X → Prop l2)
  (η : (x : X) → type-Prop (Q (intro-double-negation x)))
  (y : ¬¬ X)
  where

  prop-double-negation-excluded-middle-oracle-induction :
    Prop (l1 ⊔ l2)
  prop-double-negation-excluded-middle-oracle-induction =
    Σ-Prop (double-negation-type-Prop X) Q

  map-double-negation-excluded-middle-oracle-induction :
    is-decidable-type-Prop
      prop-double-negation-excluded-middle-oracle-induction →
    ¬¬ X
  map-double-negation-excluded-middle-oracle-induction =
    rec-coproduct pr1 (λ _ → y)

  section-double-negation-excluded-middle-oracle-induction :
    ( d :
      is-decidable-type-Prop
        prop-double-negation-excluded-middle-oracle-induction) →
    type-Prop (Q (map-double-negation-excluded-middle-oracle-induction d))
  section-double-negation-excluded-middle-oracle-induction (inl z) =
    pr2 z
  section-double-negation-excluded-middle-oracle-induction (inr n) =
    ex-falso (y (λ x → n (intro-double-negation x , η x)))
```

```agda
module _
  {l1 l2 : Level}
  {X : UU l1}
  where

  ind-double-negation-excluded-middle-oracle :
    dependent-extension-property-oracle-reflection-Level
      ( l2)
      ( excluded-middle-oracle)
      ( X)
      ( double-negation-type-Prop X)
      ( oracle-algebra-double-negation-excluded-middle-oracle l2)
  ind-double-negation-excluded-middle-oracle Q η ask y =
    tr
      ( type-Prop ∘ Q)
      ( eq-is-prop is-prop-double-negation)
      ( ask
        ( prop-double-negation-excluded-middle-oracle-induction Q η y)
        ( map-double-negation-excluded-middle-oracle-induction Q η y)
        ( section-double-negation-excluded-middle-oracle-induction Q η y))

  oracle-reflection-double-negation-excluded-middle-oracle :
    oracle-reflection l1 l2 excluded-middle-oracle X
  oracle-reflection-double-negation-excluded-middle-oracle =
    ( double-negation-type-Prop X ,
      oracle-algebra-double-negation-excluded-middle-oracle l2 ,
      ind-double-negation-excluded-middle-oracle)

excluded-middle-oracle-modality :
  (l1 l2 : Level) →
  oracle-modality l1 l1 l2 excluded-middle-oracle
excluded-middle-oracle-modality l1 l2 X =
  oracle-reflection-double-negation-excluded-middle-oracle
```

## See also

- [Double negation sheaves](orthogonal-factorization-systems.double-negation-sheaves.md)
