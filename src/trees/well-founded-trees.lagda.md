# Well-founded trees

```agda
module trees.well-founded-trees where
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

A {{#concept "well-founded tree" Agda=Well-Founded-Tree}} is a
[transitive](foundation.binary-relations.md)
[well-founded relation](order-theory.well-founded-relations.md).

## Definitions

### The predicate of being a well-founded tree

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Relation l2 X)
  where

  is-well-founded-tree-Relation : UU (l1 ⊔ l2)
  is-well-founded-tree-Relation =
    is-well-founded-Relation R × is-transitive R
```

### Well-founded trees

```agda
Well-Founded-Tree : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Well-Founded-Tree l1 l2 =
  Σ (UU l1) (λ X → Σ (Relation l2 X) is-well-founded-tree-Relation)

module _
  {l1 l2 : Level} (P : Well-Founded-Tree l1 l2)
  where

  type-Well-Founded-Tree : UU l1
  type-Well-Founded-Tree = pr1 P

  le-Well-Founded-Tree : Relation l2 type-Well-Founded-Tree
  le-Well-Founded-Tree = pr1 (pr2 P)

  is-well-founded-tree-Well-Founded-Tree :
    is-well-founded-tree-Relation le-Well-Founded-Tree
  is-well-founded-tree-Well-Founded-Tree = pr2 (pr2 P)

  is-well-founded-relation-le-Well-Founded-Tree :
    is-well-founded-Relation le-Well-Founded-Tree
  is-well-founded-relation-le-Well-Founded-Tree =
    pr1 is-well-founded-tree-Well-Founded-Tree

  is-transitive-le-Well-Founded-Tree :
    is-transitive le-Well-Founded-Tree
  is-transitive-le-Well-Founded-Tree =
    pr2 is-well-founded-tree-Well-Founded-Tree

  well-founded-relation-Well-Founded-Tree :
    Well-Founded-Relation l2 type-Well-Founded-Tree
  pr1 well-founded-relation-Well-Founded-Tree =
    le-Well-Founded-Tree
  pr2 well-founded-relation-Well-Founded-Tree =
    is-well-founded-relation-le-Well-Founded-Tree

  is-asymmetric-le-Well-Founded-Tree :
    is-asymmetric le-Well-Founded-Tree
  is-asymmetric-le-Well-Founded-Tree =
    is-asymmetric-le-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Tree)

  is-irreflexive-le-Well-Founded-Tree :
    is-irreflexive le-Well-Founded-Tree
  is-irreflexive-le-Well-Founded-Tree =
    is-irreflexive-le-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Tree)
```

### The containment relation on a well-founded tree

Given a well-founded tree `P` there is an associated reflexive relation given by

$$
  (x ≤ y) := (u : X) → u ∈ x → u ∈ y.
$$

```agda
module _
  {l1 l2 : Level} (P : Well-Founded-Tree l1 l2)
  where

  leq-Well-Founded-Tree : Relation (l1 ⊔ l2) (type-Well-Founded-Tree P)
  leq-Well-Founded-Tree =
    leq-Well-Founded-Relation (well-founded-relation-Well-Founded-Tree P)

  refl-leq-Well-Founded-Tree :
    is-reflexive leq-Well-Founded-Tree
  refl-leq-Well-Founded-Tree =
    refl-leq-Well-Founded-Relation (well-founded-relation-Well-Founded-Tree P)

  transitive-leq-Well-Founded-Tree :
    is-transitive leq-Well-Founded-Tree
  transitive-leq-Well-Founded-Tree =
    transitive-leq-Well-Founded-Relation
      ( well-founded-relation-Well-Founded-Tree P)
```
