# Strictly preordered types

```agda
module order-theory.strictly-preordered-types where
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

A {{#concept "strictly preordered type" Agda=Strictly-Preordered-Type}} consists
of a type $A$, a [binary relation](foundation.binary-relations.md) $<$ on $A$
valued in the [propositions](foundation-core.propositions.md), such that the
relation $<$ is irreflexive and transitive:

- For any $x:A$ we have $x \nle x$.
- For any $x,y,z:A$ we have $y<z \to x<y \to x<z$.

Strictly preordered types satisfy antisymmetry by irreflexivity and
transitivity.

## Definitions

### The type of strictly preordered types

```agda
Strictly-Preordered-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strictly-Preordered-Type l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( Relation-Prop l2 A)
        ( λ R → is-irreflexive-Relation-Prop R × is-transitive-Relation-Prop R))

module _
  {l1 l2 : Level} (A : Strictly-Preordered-Type l1 l2)
  where

  type-Strictly-Preordered-Type :
    UU l1
  type-Strictly-Preordered-Type =
    pr1 A

  le-prop-Strictly-Preordered-Type :
    Relation-Prop l2 type-Strictly-Preordered-Type
  le-prop-Strictly-Preordered-Type =
    pr1 (pr2 A)

  le-Strictly-Preordered-Type :
    Relation l2 type-Strictly-Preordered-Type
  le-Strictly-Preordered-Type =
    type-Relation-Prop le-prop-Strictly-Preordered-Type

  is-prop-le-Strictly-Preordered-Type :
    (x y : type-Strictly-Preordered-Type) →
    is-prop (le-Strictly-Preordered-Type x y)
  is-prop-le-Strictly-Preordered-Type =
    is-prop-type-Relation-Prop le-prop-Strictly-Preordered-Type

  is-irreflexive-le-Strictly-Preordered-Type :
    is-irreflexive le-Strictly-Preordered-Type
  is-irreflexive-le-Strictly-Preordered-Type =
    pr1 (pr2 (pr2 A))

  is-transitive-le-Strictly-Preordered-Type :
    is-transitive le-Strictly-Preordered-Type
  is-transitive-le-Strictly-Preordered-Type =
    pr2 (pr2 (pr2 A))
```

## Properties

### The ordering of a strictly preordered type is antisymmetric

```agda
module _
  {l1 l2 : Level} (A : Strictly-Preordered-Type l1 l2)
  where

  is-antisymmetric-le-Strictly-Preordered-Type :
    is-antisymmetric (le-Strictly-Preordered-Type A)
  is-antisymmetric-le-Strictly-Preordered-Type x y H K =
    ex-falso
      ( is-irreflexive-le-Strictly-Preordered-Type A x
        ( is-transitive-le-Strictly-Preordered-Type A x y x K H))
```
