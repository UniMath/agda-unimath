# Well-founded orders

```agda
module order-theory.well-founded-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.well-founded-relations
```

</details>

## Idea

A **well-founded order** is a [transitive](foundation.binary-relations.md)
[well-founded relation](order-theory.well-founded-relations.md).

## Definitions

### The predicate of being a well-founded order

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Relation l2 X)
  where

  is-well-founded-order-Relation : UU (l1 ⊔ l2)
  is-well-founded-order-Relation = is-transitive R × is-well-founded-Relation R
```

### Well-founded orders

```agda
Well-Founded-Order : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Well-Founded-Order l2 X = Σ (Relation l2 X) is-well-founded-order-Relation

module _
  {l1 l2 : Level} {X : UU l1} (R : Well-Founded-Order l2 X)
  where

  rel-Well-Founded-Order : Relation l2 X
  rel-Well-Founded-Order = pr1 R

  is-well-founded-order-Well-Founded-Order :
    is-well-founded-order-Relation rel-Well-Founded-Order
  is-well-founded-order-Well-Founded-Order = pr2 R

  is-transitive-Well-Founded-Order : is-transitive rel-Well-Founded-Order
  is-transitive-Well-Founded-Order =
    pr1 is-well-founded-order-Well-Founded-Order

  is-well-founded-relation-Well-Founded-Order :
    is-well-founded-Relation rel-Well-Founded-Order
  is-well-founded-relation-Well-Founded-Order =
    pr2 is-well-founded-order-Well-Founded-Order

  well-founded-relation-Well-Founded-Order : Well-Founded-Relation l2 X
  pr1 well-founded-relation-Well-Founded-Order =
    rel-Well-Founded-Order
  pr2 well-founded-relation-Well-Founded-Order =
    is-well-founded-relation-Well-Founded-Order

  is-asymmetric-Well-Founded-Order :
    is-asymmetric rel-Well-Founded-Order
  is-asymmetric-Well-Founded-Order =
    is-asymmetric-Well-Founded-Relation well-founded-relation-Well-Founded-Order

  is-irreflexive-Well-Founded-Order :
    is-irreflexive rel-Well-Founded-Order
  is-irreflexive-Well-Founded-Order =
    is-irreflexive-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Order)
```
