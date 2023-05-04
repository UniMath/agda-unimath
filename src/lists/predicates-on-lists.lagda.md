# Predicates on lists

```agda
module lists.predicates-on-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Idea

In these file we define predicates on lists.

## Definitions

### For all

```agda
module _
  {l1 l2 : Level} (X : UU l1) (P : X → Prop l2)
  where

  for-all-list-Prop :
    (l : list X) → Prop l2
  for-all-list-Prop nil = raise-unit-Prop l2
  for-all-list-Prop (cons x l) = prod-Prop (P x) (for-all-list-Prop l)

  for-all-list :
    (l : list X) → UU l2
  for-all-list l = type-Prop (for-all-list-Prop l)

  is-prop-for-all-list :
    (l : list X) → is-prop (for-all-list l)
  is-prop-for-all-list l = is-prop-type-Prop (for-all-list-Prop l)
```

### Exists

```agda
```
