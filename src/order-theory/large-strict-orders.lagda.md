# Large strict orders

```agda
module order-theory.large-strict-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-relations
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-strict-preorders
open import order-theory.similarity-of-elements-large-strict-preorders
open import order-theory.strict-orders
open import order-theory.strict-preorders
open import order-theory.strictly-preordered-sets
```

</details>

## Idea

A {{#concept "large strict order" Agda=Large-Strict-Order}} is a
[large strict preorder](order-theory.large-strict-preorders.md) $A$ satisfying
the
{{#concept "extensionality principle" Disambiguation="of large strict orders" Agda=extensionality-principle-Large-Strict-Preorder}}
that pairs of elements at a universe level that are
[similar](order-theory.similarity-of-elements-large-strict-preorders.md)
relative to that same universe level are
[equal](foundation-core.identity-types.md). More concretely, if $x$ and $y$ are
elements at universe level $l$ such that for every other element $z$ at the same
universe level $l$, we have

- $z < x$ [if and only if](foundation.logical-equivalences.md) $z < y$, and
- $x < z$ if and only if $y < z$,

then $x = y$.

The extensionality principle of large strict orders is slightly different to
that of [ordinals](order-theory.ordinals.md). For ordinals, elements are equal
already if they are _similar from below_. Namely, only the first of the two
conditions above must be satisfied in order for two elements to be equal.

The extensionality principle of large strict orders can be recovered as a
special case of the extensionality principle of
[semicategories](category-theory.nonunital-precategories.md) as considered in
Example 8.16 of _The Univalence Principle_ {{#cite ANST25}}.

## Definitions

### The extensionality principle of large strict orders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Preorder α β)
  where

  extensionality-principle-level-Large-Strict-Preorder :
    (l : Level) → UU (α l ⊔ β l l)
  extensionality-principle-level-Large-Strict-Preorder l =
    (x y : type-Large-Strict-Preorder A l) →
    sim-level-Large-Strict-Preorder A l x y →
    x ＝ y

  extensionality-principle-Large-Strict-Preorder : UUω
  extensionality-principle-Large-Strict-Preorder =
    {l : Level} → extensionality-principle-level-Large-Strict-Preorder l

  weak-extensionality-principle-level-Large-Strict-Preorder : Level → UUω
  weak-extensionality-principle-level-Large-Strict-Preorder l =
    (x y : type-Large-Strict-Preorder A l) →
    sim-Large-Strict-Preorder A x y →
    x ＝ y

  weak-extensionality-principle-Large-Strict-Preorder : UUω
  weak-extensionality-principle-Large-Strict-Preorder =
    {l : Level} → weak-extensionality-principle-level-Large-Strict-Preorder l
```

The last, "weak", extensionality principle asks that $x$ and $y$ at universe
level $l$ are similar relative to _every_ universe level in order to conclude
they are equal. This principle is likely too weak for practical purposes. For
instance, it is no longer the case for "weakly extensional" large strict
preorders that the underlying strict preorder at a universe level is
extensional, nor can we conclude that the underlying hierarchy of types of a
weakly extensional large strict preorder is a hierarchy of sets without
formalizing the concept of "large propositions", i.e., `Propω`.

### The type of large strict orders

```agda
record Large-Strict-Order (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor make-Large-Strict-Order
  field
    large-strict-preorder-Large-Strict-Order : Large-Strict-Preorder α β

    extensionality-Large-Strict-Order :
      extensionality-principle-Large-Strict-Preorder
        large-strict-preorder-Large-Strict-Order

  type-Large-Strict-Order : (l : Level) → UU (α l)
  type-Large-Strict-Order =
    type-Large-Strict-Preorder large-strict-preorder-Large-Strict-Order

  le-Large-Strict-Order :
    Large-Relation β type-Large-Strict-Order
  le-Large-Strict-Order =
    le-Large-Strict-Preorder large-strict-preorder-Large-Strict-Order

  is-prop-le-Large-Strict-Order :
    {l1 l2 : Level}
    (x : type-Large-Strict-Order l1)
    (y : type-Large-Strict-Order l2) →
    is-prop (le-Large-Strict-Order x y)
  is-prop-le-Large-Strict-Order =
    is-prop-le-Large-Strict-Preorder large-strict-preorder-Large-Strict-Order

  le-prop-Large-Strict-Order : Large-Relation-Prop β type-Large-Strict-Order
  le-prop-Large-Strict-Order =
    le-prop-Large-Strict-Preorder large-strict-preorder-Large-Strict-Order

  is-irreflexive-le-Large-Strict-Order :
    is-antireflexive-Large-Relation
      type-Large-Strict-Order
      le-Large-Strict-Order
  is-irreflexive-le-Large-Strict-Order =
    is-irreflexive-le-Large-Strict-Preorder
      large-strict-preorder-Large-Strict-Order

  is-transitive-le-Large-Strict-Order :
    is-transitive-Large-Relation type-Large-Strict-Order le-Large-Strict-Order
  is-transitive-le-Large-Strict-Order =
    transitive-le-Large-Strict-Preorder large-strict-preorder-Large-Strict-Order

open Large-Strict-Order public
```

### The underlying strict order at a universe level

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  strict-preorder-Large-Strict-Order :
    (l : Level) → Strict-Preorder (α l) (β l l)
  strict-preorder-Large-Strict-Order =
    strict-preorder-Large-Strict-Preorder
      ( large-strict-preorder-Large-Strict-Order A)

  extensionality-strict-preorder-Large-Strict-Order :
    (l : Level) →
    extensionality-principle-Strict-Preorder
      ( strict-preorder-Large-Strict-Order l)
  extensionality-strict-preorder-Large-Strict-Order l =
    extensionality-Large-Strict-Order A

  strict-order-Large-Strict-Order :
    (l : Level) → Strict-Order (α l) (β l l)
  strict-order-Large-Strict-Order l =
    ( strict-preorder-Large-Strict-Order l ,
      extensionality-strict-preorder-Large-Strict-Order l)
```

## Properties

### The underlying hierarchy of types is a hierarchy of sets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Order α β)
  where

  is-set-type-Large-Strict-Order :
    {l : Level} → is-set (type-Large-Strict-Order A l)
  is-set-type-Large-Strict-Order {l} =
    is-set-type-Strict-Order (strict-order-Large-Strict-Order A l)

  set-Large-Strict-Order : (l : Level) → Set (α l)
  set-Large-Strict-Order l =
    set-Strict-Order (strict-order-Large-Strict-Order A l)
```

### The extensionality principle is a proposition at every universe level

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Strict-Preorder α β)
  where

  is-prop-extensionality-principle-level-Large-Strict-Preorder :
    {l : Level} →
    is-prop (extensionality-principle-level-Large-Strict-Preorder A l)
  is-prop-extensionality-principle-level-Large-Strict-Preorder {l} =
    is-prop-extensionality-principle-Strict-Preorder
      ( strict-preorder-Large-Strict-Preorder A l)

  extensionality-principle-level-prop-Large-Strict-Preorder :
    (l : Level) → Prop (α l ⊔ β l l)
  extensionality-principle-level-prop-Large-Strict-Preorder l =
    ( extensionality-principle-level-Large-Strict-Preorder A l ,
      is-prop-extensionality-principle-level-Large-Strict-Preorder)
```

## References

{{#bibliography}}
