# Trichotomous strict orders

```agda
module order-theory.trichotomous-strict-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.cotransitive-strict-orders
open import order-theory.strict-orders
open import order-theory.strict-preorders
open import order-theory.trichotomous-strict-preorders
```

</details>

## Idea

A [strict order](order-theory.strict-orders.md) is
{{#concept "trichotomous" Disambiguation="strict order" Agda=is-trichotomous-Strict-Order Agda=Trichotomous-Strict-Order}}
if for every two elements `x` and `y`, either `x < y`, `x ＝ y`, or `y < x`.

## Definitions

### The predicate on strict orders of being trichotomous

```agda
is-trichotomous-Strict-Order :
  {l1 l2 : Level} → Strict-Order l1 l2 → UU (l1 ⊔ l2)
is-trichotomous-Strict-Order A =
  is-trichotomous-Strict-Preorder (strict-preorder-Strict-Order A)
```

### The type of trichotomous strict orders

```agda
Trichotomous-Strict-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Trichotomous-Strict-Order l1 l2 =
  Σ (Strict-Order l1 l2) is-trichotomous-Strict-Order

module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Order l1 l2)
  where

  strict-order-Trichotomous-Strict-Order : Strict-Order l1 l2
  strict-order-Trichotomous-Strict-Order = pr1 A

  strict-preorder-Trichotomous-Strict-Order : Strict-Preorder l1 l2
  strict-preorder-Trichotomous-Strict-Order =
    strict-preorder-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  extensionality-Trichotomous-Strict-Order :
    extensionality-principle-Strict-Preorder
      ( strict-preorder-Trichotomous-Strict-Order)
  extensionality-Trichotomous-Strict-Order =
    extensionality-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  type-Trichotomous-Strict-Order : UU l1
  type-Trichotomous-Strict-Order =
    type-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  le-prop-Trichotomous-Strict-Order :
    Relation-Prop l2 type-Trichotomous-Strict-Order
  le-prop-Trichotomous-Strict-Order =
    le-prop-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  le-Trichotomous-Strict-Order :
    Relation l2 type-Trichotomous-Strict-Order
  le-Trichotomous-Strict-Order =
    le-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  is-prop-le-Trichotomous-Strict-Order :
    (x y : type-Trichotomous-Strict-Order) →
    is-prop (le-Trichotomous-Strict-Order x y)
  is-prop-le-Trichotomous-Strict-Order =
    is-prop-le-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  is-irreflexive-le-Trichotomous-Strict-Order :
    is-irreflexive le-Trichotomous-Strict-Order
  is-irreflexive-le-Trichotomous-Strict-Order =
    is-irreflexive-le-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  is-transitive-le-Trichotomous-Strict-Order :
    is-transitive le-Trichotomous-Strict-Order
  is-transitive-le-Trichotomous-Strict-Order =
    is-transitive-le-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)

  is-trichotomous-Strict-Order-Trichotomous-Strict-Order :
    is-trichotomous-Strict-Order
      ( strict-order-Trichotomous-Strict-Order)
  is-trichotomous-Strict-Order-Trichotomous-Strict-Order =
    pr2 A

  trichotomous-strict-preorder-Trichotomous-Strict-Order :
    Trichotomous-Strict-Preorder l1 l2
  trichotomous-strict-preorder-Trichotomous-Strict-Order =
    ( strict-preorder-Trichotomous-Strict-Order ,
      is-trichotomous-Strict-Order-Trichotomous-Strict-Order)
```

## Properties

### Being trichotomous is a property

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Order l1 l2)
  where

  is-prop-is-trichotomous-Strict-Order :
    is-prop (is-trichotomous-Strict-Order A)
  is-prop-is-trichotomous-Strict-Order =
    is-prop-is-trichotomous-Strict-Preorder
      ( strict-preorder-Strict-Order A)

  is-trichotomous-prop-Strict-Order : Prop (l1 ⊔ l2)
  is-trichotomous-prop-Strict-Order =
    is-trichotomous-prop-Strict-Preorder
      ( strict-preorder-Strict-Order A)
```

### Trichotomy implies weak trichotomy

```agda
module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Order l1 l2)
  where

  ge-not-eq-not-le-Trichotomous-Strict-Order :
    (x y : type-Trichotomous-Strict-Order A) →
    ¬ le-Trichotomous-Strict-Order A x y →
    ¬ (x ＝ y) →
    le-Trichotomous-Strict-Order A y x
  ge-not-eq-not-le-Trichotomous-Strict-Order =
    ge-not-eq-not-le-Trichotomous-Strict-Preorder
      ( trichotomous-strict-preorder-Trichotomous-Strict-Order A)
```

### Trichotomous strict orders are cotransitive

```agda
module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Order l1 l2)
  where

  is-cotransitive-le-Trichotomous-Strict-Order :
    is-cotransitive-le-Strict-Order
      ( strict-order-Trichotomous-Strict-Order A)
  is-cotransitive-le-Trichotomous-Strict-Order =
    is-cotransitive-le-Trichotomous-Strict-Preorder
      ( trichotomous-strict-preorder-Trichotomous-Strict-Order A)
```

### Trichotomous strict orders are decidable

```agda
module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Order l1 l2)
  where

  is-decidable-le-Trichotomous-Strict-Order :
    (x y : type-Trichotomous-Strict-Order A) →
    is-decidable (le-Trichotomous-Strict-Order A x y)
  is-decidable-le-Trichotomous-Strict-Order =
    is-decidable-le-Trichotomous-Strict-Preorder
      ( trichotomous-strict-preorder-Trichotomous-Strict-Order A)

  is-decidable-eq-Trichotomous-Strict-Order :
    (x y : type-Trichotomous-Strict-Order A) → is-decidable (x ＝ y)
  is-decidable-eq-Trichotomous-Strict-Order =
    is-decidable-eq-Trichotomous-Strict-Preorder
      ( trichotomous-strict-preorder-Trichotomous-Strict-Order A)

  has-decidable-equality-Trichotomous-Strict-Order :
    has-decidable-equality (type-Trichotomous-Strict-Order A)
  has-decidable-equality-Trichotomous-Strict-Order =
    has-decidable-equality-Trichotomous-Strict-Preorder
      ( trichotomous-strict-preorder-Trichotomous-Strict-Order A)

module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Order l1 l2)
  where

  discrete-type-Trichotomous-Strict-Order : Discrete-Type l1
  discrete-type-Trichotomous-Strict-Order =
    ( type-Trichotomous-Strict-Order A ,
      has-decidable-equality-Trichotomous-Strict-Order A)
```

### Decidable strict orders with extensional incomparability are trichotomous

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Order l1 l2)
  (dle-A : (x y : type-Strict-Order A) → is-decidable (le-Strict-Order A x y))
  (eq-incomparable-A :
    (x y : type-Strict-Order A) →
    ¬ le-Strict-Order A x y →
    ¬ le-Strict-Order A y x →
    x ＝ y)
  where

  is-trichotomous-is-decidable-le-eq-incomparable-Strict-Order :
    is-trichotomous-Strict-Order A
  is-trichotomous-is-decidable-le-eq-incomparable-Strict-Order =
    is-trichotomous-is-decidable-le-eq-incomparable-Strict-Preorder
      ( strict-preorder-Strict-Order A)
      ( dle-A)
      ( eq-incomparable-A)
```
