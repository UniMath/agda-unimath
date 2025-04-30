# Large strict preorders

```agda
module order-theory.large-strict-preorders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels

open import order-theory.strict-preorders
```

</details>

## Idea

A {{#concept "large strict preorder" Agda=Large-Strict-Preorder}} consists of a
hierarchy of types $A$ indexed by universe levels, a
[large binary relation](foundation.large-binary-relations.md) $<$ on $A$ valued
in the [propositions](foundation-core.propositions.md), such that the relation
$<$ is irreflexive and transitive:

- For any $x:A$ we have $x ≮ x$.
- For any $x,y,z:A$ we have $(y<z) → (x<y) → (x<z)$.

Note that large strict preorders satisfy antisymmetry by irreflexivity and
transitivity, but this is not the correct extensionality principle for strict
preorders. The correct extensionality principle is considered on the page on
[large strict orders](order-theory.large-strict-orders.md).

## Definitions

### Large strict preorders

```agda
record
  Large-Strict-Preorder
  (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Strict-Preorder
  field
    type-Large-Strict-Preorder : (l : Level) → UU (α l)

    le-prop-Large-Strict-Preorder :
      Large-Relation-Prop β type-Large-Strict-Preorder

  le-Large-Strict-Preorder : Large-Relation β type-Large-Strict-Preorder
  le-Large-Strict-Preorder x y = type-Prop (le-prop-Large-Strict-Preorder x y)

  is-prop-le-Large-Strict-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Strict-Preorder l1)
    (y : type-Large-Strict-Preorder l2) →
    is-prop (le-Large-Strict-Preorder x y)
  is-prop-le-Large-Strict-Preorder x y =
    is-prop-type-Prop (le-prop-Large-Strict-Preorder x y)

  field
    is-irreflexive-le-Large-Strict-Preorder :
      is-antireflexive-Large-Relation
        ( type-Large-Strict-Preorder)
        ( le-Large-Strict-Preorder)

    transitive-le-Large-Strict-Preorder :
      is-transitive-Large-Relation
        ( type-Large-Strict-Preorder)
        ( le-Large-Strict-Preorder)

open Large-Strict-Preorder public
```

### The underlying strict preorder at a universe level

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Strict-Preorder α β)
  where

  strict-preorder-Large-Strict-Preorder :
    (l : Level) → Strict-Preorder (α l) (β l l)
  strict-preorder-Large-Strict-Preorder l =
    ( type-Large-Strict-Preorder P l ,
      le-prop-Large-Strict-Preorder P ,
      is-irreflexive-le-Large-Strict-Preorder P ,
      transitive-le-Large-Strict-Preorder P)
```
