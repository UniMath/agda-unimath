# Strictly ordered types

```agda
module order-theory.strictly-ordered-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "strictly ordered type" Agda=Strictly-Ordered-Type}} consists of a
type $A$, a [binary relation](foundation.binary-relations.md) $<$ on $A$ valued
in the [propositions](foundation-core.propositions.md), such that the relation
$<$ is {{#concept "irreflexive"}} and transitive:

- For any $x:A$ we have $x \nle x$.
- For any $x,y,z:A$ we have $y<z \to x<y \to x<z$.

Strictly ordered types satisfy antisymmetry by irreflexivity and transitivity.

## Definitions

### The type of strictly ordered types

```agda
Strictly-Ordered-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strictly-Ordered-Type l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( Relation-Prop l2 A)
        ( λ R → is-irreflexive-Relation-Prop R × is-transitive-Relation-Prop R))

module _
  {l1 l2 : Level} (A : Strictly-Ordered-Type l1 l2)
  where

  type-Strictly-Ordered-Type :
    UU l1
  type-Strictly-Ordered-Type =
    pr1 A

  le-prop-Strictly-Ordered-Type :
    Relation-Prop l2 type-Strictly-Ordered-Type
  le-prop-Strictly-Ordered-Type =
    pr1 (pr2 A)

  le-Strictly-Ordered-Type :
    Relation l2 type-Strictly-Ordered-Type
  le-Strictly-Ordered-Type =
    type-Relation-Prop le-prop-Strictly-Ordered-Type

  is-prop-le-Strictly-Ordered-Type :
    (x y : type-Strictly-Ordered-Type) → is-prop (le-Strictly-Ordered-Type x y)
  is-prop-le-Strictly-Ordered-Type =
    is-prop-type-Relation-Prop le-prop-Strictly-Ordered-Type

  is-irreflexive-le-Strictly-Ordered-Type :
    is-irreflexive le-Strictly-Ordered-Type
  is-irreflexive-le-Strictly-Ordered-Type =
    pr1 (pr2 (pr2 A))

  is-transitive-le-Strictly-Ordered-Type :
    is-transitive le-Strictly-Ordered-Type
  is-transitive-le-Strictly-Ordered-Type =
    pr2 (pr2 (pr2 A))
```

## Properties

### The ordering of a strictly ordered type is antisymmetric

```agda
module _
  {l1 l2 : Level} (A : Strictly-Ordered-Type l1 l2)
  where

  is-antisymmetric-le-Strictly-Ordered-Type :
    is-antisymmetric (le-Strictly-Ordered-Type A)
  is-antisymmetric-le-Strictly-Ordered-Type x y H K =
    ex-falso
      ( is-irreflexive-le-Strictly-Ordered-Type A x
        ( is-transitive-le-Strictly-Ordered-Type A x y x K H))
```
