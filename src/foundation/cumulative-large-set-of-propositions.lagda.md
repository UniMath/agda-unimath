# The cumulative large set of propositions

```agda
module foundation.cumulative-large-set-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels
open import foundation.logical-equivalences
open import foundation.raising-universe-levels
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.large-locale-of-propositions
```

</details>

## Idea

## Definition

```agda
raise-Prop : {l1 : Level} (l : Level) → Prop l1 → Prop (l ⊔ l1)
pr1 (raise-Prop l P) = raise l (type-Prop P)
pr2 (raise-Prop l P) =
  is-prop-equiv' (compute-raise l (type-Prop P)) (is-prop-type-Prop P)

iff-raise-Prop :
  {l1 : Level} (l : Level) (P : Prop l1) → type-iff-Prop P (raise-Prop l P)
iff-raise-Prop l P = (map-raise , map-inv-raise)

cumulative-large-set-Prop : Cumulative-Large-Set lsuc (_⊔_)
cumulative-large-set-Prop =
  λ where
    .type-Cumulative-Large-Set → Prop
    .large-similarity-relation-Cumulative-Large-Set →
      large-similarity-relation-Prop
    .raise-Cumulative-Large-Set → raise-Prop
    .sim-raise-Cumulative-Large-Set → iff-raise-Prop
```

## Properties

### Conjunction is a similarity-preserving binary operation

```agda

```
