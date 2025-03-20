# Predicates on lists

```agda
open import foundation.function-extensionality-axiom

module
  lists.predicates-on-lists
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions funext
open import foundation.raising-universe-levels-unit-type funext
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Definitions

### For all

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
