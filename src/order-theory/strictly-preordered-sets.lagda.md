# Strictly preordered sets

```agda
module order-theory.strictly-preordered-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.strict-preorders
```

</details>

## Idea

A {{#concept "strictly preordered set" Agda=Strictly-Preordered-Set}} is a
[strictly preordered type](order-theory.strict-preorders.md) whose underlying
type is a [set](foundation-core.sets.md). More specifically, a strictly
preordered set consists of a set $A$, a
[binary relation](foundation.binary-relations.md) $<$ on $A$ valued in the
[propositions](foundation-core.propositions.md), such that the relation $<$ is
irreflexive and transitive:

- For any $x:A$ we have $x \nless x$.
- For any $x,y,z:A$ we have $(y<z) → (x<y) → (x<z)$.

Strictly preordered sets satisfy antisymmetry by irreflexivity and transitivity.

## Definitions

### The type of strictly preordered sets

```agda
Strictly-Preordered-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strictly-Preordered-Set l1 l2 =
  Σ ( Set l1)
    ( λ A →
      Σ ( Relation-Prop l2 (type-Set A))
        ( λ R → is-irreflexive-Relation-Prop R × is-transitive-Relation-Prop R))

make-Strictly-Preordered-Set :
  {l1 l2 : Level}
  (P : Strict-Preorder l1 l2) →
  is-set (type-Strict-Preorder P) →
  Strictly-Preordered-Set l1 l2
make-Strictly-Preordered-Set P is-set-P =
  ( ( type-Strict-Preorder P , is-set-P) , pr2 P)

module _
  {l1 l2 : Level} (A : Strictly-Preordered-Set l1 l2)
  where

  set-Strictly-Preordered-Set :
    Set l1
  set-Strictly-Preordered-Set =
    pr1 A

  type-Strictly-Preordered-Set :
    UU l1
  type-Strictly-Preordered-Set =
    type-Set set-Strictly-Preordered-Set

  is-set-type-Strictly-Preordered-Set :
    is-set type-Strictly-Preordered-Set
  is-set-type-Strictly-Preordered-Set =
    is-set-type-Set set-Strictly-Preordered-Set

  le-prop-Strictly-Preordered-Set :
    Relation-Prop l2 type-Strictly-Preordered-Set
  le-prop-Strictly-Preordered-Set =
    pr1 (pr2 A)

  le-Strictly-Preordered-Set :
    Relation l2 type-Strictly-Preordered-Set
  le-Strictly-Preordered-Set =
    rel-Relation-Prop le-prop-Strictly-Preordered-Set

  is-prop-le-Strictly-Preordered-Set :
    (x y : type-Strictly-Preordered-Set) →
    is-prop (le-Strictly-Preordered-Set x y)
  is-prop-le-Strictly-Preordered-Set =
    is-prop-rel-Relation-Prop le-prop-Strictly-Preordered-Set

  is-irreflexive-le-Strictly-Preordered-Set :
    is-irreflexive le-Strictly-Preordered-Set
  is-irreflexive-le-Strictly-Preordered-Set =
    pr1 (pr2 (pr2 A))

  is-transitive-le-Strictly-Preordered-Set :
    is-transitive le-Strictly-Preordered-Set
  is-transitive-le-Strictly-Preordered-Set =
    pr2 (pr2 (pr2 A))

  strict-preorder-Strictly-Preordered-Set :
    Strict-Preorder l1 l2
  pr1 strict-preorder-Strictly-Preordered-Set =
    type-Strictly-Preordered-Set
  pr1 (pr2 strict-preorder-Strictly-Preordered-Set) =
    le-prop-Strictly-Preordered-Set
  pr1 (pr2 (pr2 strict-preorder-Strictly-Preordered-Set)) =
    is-irreflexive-le-Strictly-Preordered-Set
  pr2 (pr2 (pr2 strict-preorder-Strictly-Preordered-Set)) =
    is-transitive-le-Strictly-Preordered-Set
```

## Properties

### The ordering of a strictly preordered set is antisymmetric

```agda
module _
  {l1 l2 : Level} (A : Strictly-Preordered-Set l1 l2)
  where

  is-antisymmetric-le-Strictly-Preordered-Set :
    is-antisymmetric (le-Strictly-Preordered-Set A)
  is-antisymmetric-le-Strictly-Preordered-Set =
    is-antisymmetric-le-Strict-Preorder
      ( strict-preorder-Strictly-Preordered-Set A)
```

## See also

- [Strict orders](order-theory.strict-orders.md) are strictly preordered sets
  that are _extensional_ with respect to the structure of the underlying strict
  preorder.
