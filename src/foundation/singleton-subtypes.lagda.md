# Singleton subtypes

```agda
module foundation.singleton-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A singleton subtype of a type `X` is a subtype `P` of `X` of which the underlying type is contractible.

## Definition

### General singleton subtypes

```agda
is-singleton-subtype-Prop :
  {l1 l2 : Level} {X : UU l1} → subtype l2 X → Prop (l1 ⊔ l2)
is-singleton-subtype-Prop P = is-contr-Prop (type-subtype P)

is-singleton-subtype :
  {l1 l2 : Level} {X : UU l1} → subtype l2 X → UU (l1 ⊔ l2)
is-singleton-subtype P = type-Prop (is-singleton-subtype-Prop P)

is-prop-is-singleton-subtype :
  {l1 l2 : Level} {X : UU l1} (P : subtype l2 X) →
  is-prop (is-singleton-subtype P)
is-prop-is-singleton-subtype P = is-prop-type-Prop (is-singleton-subtype-Prop P)

singleton-subtype :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
singleton-subtype l2 X = type-subtype (is-singleton-subtype-Prop {l2 = l2} {X})

module _
  {l1 l2 : Level} {X : UU l1} (P : singleton-subtype l2 X)
  where

  subtype-singleton-subtype : subtype l2 X
  subtype-singleton-subtype = pr1 P

  is-singleton-subtype-singleton-subtype :
    is-singleton-subtype subtype-singleton-subtype
  is-singleton-subtype-singleton-subtype = pr2 P
```

### Standard singleton subtypes

```agda
subtype-standard-singleton-subtype :
  {l : Level} (X : Set l) → type-Set X → subtype l (type-Set X)
subtype-standard-singleton-subtype X x y = Id-Prop X x y

standard-singleton-subtype :
  {l : Level} (X : Set l) → type-Set X → singleton-subtype l (type-Set X)
pr1 (standard-singleton-subtype X x) = subtype-standard-singleton-subtype X x
pr2 (standard-singleton-subtype X x) = is-contr-total-path x

inhabited-subtype-standard-singleton-subtype :
  {l : Level} (X : Set l) → type-Set X → inhabited-subtype l (type-Set X)
pr1 (inhabited-subtype-standard-singleton-subtype X x) =
  subtype-standard-singleton-subtype X x
pr2 (inhabited-subtype-standard-singleton-subtype X x) =
  unit-trunc-Prop (pair x refl)
```
