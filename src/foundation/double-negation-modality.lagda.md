# The double negation modality

```agda
open import foundation.function-extensionality-axiom

module
  foundation.double-negation-modality
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.double-negation funext
open import foundation.empty-types funext
open import foundation.logical-equivalences funext
open import foundation.negation funext
open import foundation.propositions funext
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.transport-along-identifications

open import logic.double-negation-elimination funext

open import orthogonal-factorization-systems.continuation-modalities funext
open import orthogonal-factorization-systems.large-lawvere-tierney-topologies funext
open import orthogonal-factorization-systems.lawvere-tierney-topologies funext
open import orthogonal-factorization-systems.modal-operators funext
open import orthogonal-factorization-systems.types-local-at-maps funext
open import orthogonal-factorization-systems.uniquely-eliminating-modalities funext
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
