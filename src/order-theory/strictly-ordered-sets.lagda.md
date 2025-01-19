# Strictly ordered sets

```agda
module order-theory.strictly-ordered-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.strictly-ordered-types
```

</details>

## Idea

A {{#concept "strictly ordered set" Agda=Strictly-Ordered-Set}} is a [strictly ordered type](order-theory.strictly-ordered-types.md) whose underlying type is a [set](foundation-core.sets.md). More specifically, a strictly ordered set consists of a set $A$, a [binary relation](foundation.binary-relations.md) $<$ on $A$ valued in the [propositions](foundation-core.propositions.md), such that the relation $<$ is {{#concept "irreflexive"}} and transitive:

- For any $x:A$ we have $x \nle x$.
- For any $x,y,z:A$ we have $y<z \to x<y \to x<z$.

Strictly ordered sets satisfy antisymmetry by irreflexivity and transitivity.

## Definitions

### The type of strictly ordered sets

```agda
Strictly-Ordered-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strictly-Ordered-Set l1 l2 =
  Σ ( Set l1)
    ( λ A →
      Σ ( Relation-Prop l2 (type-Set A))
        ( λ R → is-irreflexive-Relation-Prop R × is-transitive-Relation-Prop R))

module _
  {l1 l2 : Level} (A : Strictly-Ordered-Set l1 l2)
  where

  set-Strictly-Ordered-Set :
    Set l1
  set-Strictly-Ordered-Set =
    pr1 A

  type-Strictly-Ordered-Set :
    UU l1
  type-Strictly-Ordered-Set =
    type-Set set-Strictly-Ordered-Set

  is-set-type-Strictly-Ordered-Set :
    is-set type-Strictly-Ordered-Set
  is-set-type-Strictly-Ordered-Set =
    is-set-type-Set set-Strictly-Ordered-Set

  le-prop-Strictly-Ordered-Set :
    Relation-Prop l2 type-Strictly-Ordered-Set
  le-prop-Strictly-Ordered-Set =
    pr1 (pr2 A)

  le-Strictly-Ordered-Set :
    Relation l2 type-Strictly-Ordered-Set
  le-Strictly-Ordered-Set =
    type-Relation-Prop le-prop-Strictly-Ordered-Set

  is-prop-le-Strictly-Ordered-Set :
    (x y : type-Strictly-Ordered-Set) → is-prop (le-Strictly-Ordered-Set x y)
  is-prop-le-Strictly-Ordered-Set =
    is-prop-type-Relation-Prop le-prop-Strictly-Ordered-Set

  is-irreflexive-le-Strictly-Ordered-Set :
    is-irreflexive le-Strictly-Ordered-Set
  is-irreflexive-le-Strictly-Ordered-Set =
    pr1 (pr2 (pr2 A))

  is-transitive-le-Strictly-Ordered-Set :
    is-transitive le-Strictly-Ordered-Set
  is-transitive-le-Strictly-Ordered-Set =
    pr2 (pr2 (pr2 A))

  strictly-ordered-type-Strictly-Ordered-Set :
    Strictly-Ordered-Type l1 l2
  pr1 strictly-ordered-type-Strictly-Ordered-Set =
    type-Strictly-Ordered-Set
  pr1 (pr2 strictly-ordered-type-Strictly-Ordered-Set) =
    le-prop-Strictly-Ordered-Set
  pr1 (pr2 (pr2 strictly-ordered-type-Strictly-Ordered-Set)) =
    is-irreflexive-le-Strictly-Ordered-Set
  pr2 (pr2 (pr2 strictly-ordered-type-Strictly-Ordered-Set)) =
    is-transitive-le-Strictly-Ordered-Set
```

## Properties

### The ordering of a strictly ordered set is antisymmetric

```agda
module _
  {l1 l2 : Level} (A : Strictly-Ordered-Set l1 l2)
  where

  is-antisymmetric-le-Strictly-Ordered-Set :
    is-antisymmetric (le-Strictly-Ordered-Set A)
  is-antisymmetric-le-Strictly-Ordered-Set =
    is-antisymmetric-le-Strictly-Ordered-Type
      ( strictly-ordered-type-Strictly-Ordered-Set A)
```
