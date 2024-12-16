# Predicates on lists

```agda
module lists.predicates-on-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Definitions

### Universal quantification over the elements of a list

```agda
module _
  {l1 l2 : Level} (X : UU l1) (P : X → Prop l2)
  where

  for-all-list-Prop :
    (l : list X) → Prop l2
  for-all-list-Prop nil = raise-unit-Prop l2
  for-all-list-Prop (cons x l) = product-Prop (P x) (for-all-list-Prop l)

  for-all-list :
    (l : list X) → UU l2
  for-all-list l = type-Prop (for-all-list-Prop l)

  is-prop-for-all-list :
    (l : list X) → is-prop (for-all-list l)
  is-prop-for-all-list l = is-prop-type-Prop (for-all-list-Prop l)
```

## Properties

### Universal quantification over the elements of the empty list

```agda
for-all-nil-list :
  {l1 l2 : Level} {X : UU l1} (P : X → Prop l2) →
  for-all-list X P nil
for-all-nil-list P = raise-star
```

### If a predicate implies another predicate, then its universal quantification over the elements of a list implies the universal-quantification of the other predicate

```agda
map-for-all-list :
  {l1 l2 l3 : Level} {X : UU l1} (P : X → Prop l2) (Q : X → Prop l3) →
  ((x : X) → type-Prop (P x) → type-Prop (Q x)) →
  (l : list X) → for-all-list X P l → for-all-list X Q l
map-for-all-list P Q f nil H = raise-star
pr1 (map-for-all-list P Q f (cons x l) (H , K)) = f _ H
pr2 (map-for-all-list P Q f (cons x l) (H , K)) = map-for-all-list P Q f l K
```
