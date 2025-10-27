# Strict preorders

```agda
module order-theory.strict-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "strict preorder" Agda=Strict-Preorder}} consists of a type $A$, a
[binary relation](foundation.binary-relations.md) $<$ on $A$ valued in the
[propositions](foundation-core.propositions.md), such that the relation $<$ is
irreflexive and transitive:

- For any $x:A$ we have $x ≮ x$.
- For any $x,y,z:A$ we have $(y<z) → (x<y) → (x<z)$.

Note that strict preorders satisfy antisymmetry by irreflexivity and
transitivity, but this is not the correct extensionality principle for strict
preorders. The correct extensionality principle is considered on the page on
[strict orders](order-theory.strict-orders.md).

## Definitions

### The type of strict preorders

```agda
Strict-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Strict-Preorder l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( Relation-Prop l2 A)
        ( λ R → is-irreflexive-Relation-Prop R × is-transitive-Relation-Prop R))

module _
  {l1 l2 : Level} (A : Strict-Preorder l1 l2)
  where

  type-Strict-Preorder :
    UU l1
  type-Strict-Preorder =
    pr1 A

  le-prop-Strict-Preorder :
    Relation-Prop l2 type-Strict-Preorder
  le-prop-Strict-Preorder =
    pr1 (pr2 A)

  le-Strict-Preorder :
    Relation l2 type-Strict-Preorder
  le-Strict-Preorder =
    type-Relation-Prop le-prop-Strict-Preorder

  is-prop-le-Strict-Preorder :
    (x y : type-Strict-Preorder) →
    is-prop (le-Strict-Preorder x y)
  is-prop-le-Strict-Preorder =
    is-prop-type-Relation-Prop le-prop-Strict-Preorder

  is-irreflexive-le-Strict-Preorder :
    is-irreflexive le-Strict-Preorder
  is-irreflexive-le-Strict-Preorder =
    pr1 (pr2 (pr2 A))

  is-transitive-le-Strict-Preorder :
    is-transitive le-Strict-Preorder
  is-transitive-le-Strict-Preorder =
    pr2 (pr2 (pr2 A))
```

## Properties

### The ordering of a strict preorder is antisymmetric

```agda
module _
  {l1 l2 : Level} (A : Strict-Preorder l1 l2)
  where

  is-antisymmetric-le-Strict-Preorder :
    is-antisymmetric (le-Strict-Preorder A)
  is-antisymmetric-le-Strict-Preorder x y H K =
    ex-falso
      ( is-irreflexive-le-Strict-Preorder A x
        ( is-transitive-le-Strict-Preorder A x y x K H))
```
