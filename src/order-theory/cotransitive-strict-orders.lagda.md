# Cotransitive strict orders

```agda
module order-theory.cotransitive-strict-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation-stable-equality
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import order-theory.cotransitive-strict-preorders
open import order-theory.double-negation-stable-strict-orders
open import order-theory.strict-orders
open import order-theory.strict-preorders
```

</details>

## Idea

A [strict order](order-theory.strict-orders.md) is
{{#concept "cotransitive" Disambiguation="strict order" Agda=is-cotransitive-le-Strict-Order Agda=Cotransitive-Strict-Order}}
if whenever `x < z`, then for any `y`, either `x < y` or `y < z`.

## Definitions

### The predicate on strict orders of being cotransitive

```agda
is-cotransitive-le-Strict-Order :
  {l1 l2 : Level} → Strict-Order l1 l2 → UU (l1 ⊔ l2)
is-cotransitive-le-Strict-Order A =
  is-cotransitive-le-Strict-Preorder
    ( strict-preorder-Strict-Order A)
```

### The type of cotransitive strict orders

```agda
Cotransitive-Strict-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cotransitive-Strict-Order l1 l2 =
  Σ (Strict-Order l1 l2) is-cotransitive-le-Strict-Order

module _
  {l1 l2 : Level} (A : Cotransitive-Strict-Order l1 l2)
  where

  strict-order-Cotransitive-Strict-Order : Strict-Order l1 l2
  strict-order-Cotransitive-Strict-Order = pr1 A

  strict-preorder-Cotransitive-Strict-Order : Strict-Preorder l1 l2
  strict-preorder-Cotransitive-Strict-Order =
    strict-preorder-Strict-Order strict-order-Cotransitive-Strict-Order

  extensionality-Cotransitive-Strict-Order :
    extensionality-principle-Strict-Preorder
      strict-preorder-Cotransitive-Strict-Order
  extensionality-Cotransitive-Strict-Order =
    extensionality-Strict-Order strict-order-Cotransitive-Strict-Order

  type-Cotransitive-Strict-Order : UU l1
  type-Cotransitive-Strict-Order =
    type-Strict-Order strict-order-Cotransitive-Strict-Order

  le-prop-Cotransitive-Strict-Order :
    Relation-Prop l2 type-Cotransitive-Strict-Order
  le-prop-Cotransitive-Strict-Order =
    le-prop-Strict-Order strict-order-Cotransitive-Strict-Order

  le-Cotransitive-Strict-Order :
    Relation l2 type-Cotransitive-Strict-Order
  le-Cotransitive-Strict-Order =
    le-Strict-Order strict-order-Cotransitive-Strict-Order

  is-prop-le-Cotransitive-Strict-Order :
    (x y : type-Cotransitive-Strict-Order) →
    is-prop (le-Cotransitive-Strict-Order x y)
  is-prop-le-Cotransitive-Strict-Order =
    is-prop-le-Strict-Order strict-order-Cotransitive-Strict-Order

  is-irreflexive-le-Cotransitive-Strict-Order :
    is-irreflexive le-Cotransitive-Strict-Order
  is-irreflexive-le-Cotransitive-Strict-Order =
    is-irreflexive-le-Strict-Order strict-order-Cotransitive-Strict-Order

  is-transitive-le-Cotransitive-Strict-Order :
    is-transitive le-Cotransitive-Strict-Order
  is-transitive-le-Cotransitive-Strict-Order =
    is-transitive-le-Strict-Order strict-order-Cotransitive-Strict-Order

  is-cotransitive-le-Cotransitive-Strict-Order :
    is-cotransitive-le-Strict-Order strict-order-Cotransitive-Strict-Order
  is-cotransitive-le-Cotransitive-Strict-Order = pr2 A

  cotransitive-strict-preorder-Cotransitive-Strict-Order :
    Cotransitive-Strict-Preorder l1 l2
  cotransitive-strict-preorder-Cotransitive-Strict-Order =
    ( strict-preorder-Cotransitive-Strict-Order ,
      is-cotransitive-le-Cotransitive-Strict-Order)
```

## Properties

### Eliminating cotransitivity by negation

```agda
module _
  {l1 l2 : Level}
  (A : Cotransitive-Strict-Order l1 l2)
  where abstract

  right-le-left-nle-Cotransitive-Strict-Order :
    (x y z : type-Cotransitive-Strict-Order A) →
    le-Cotransitive-Strict-Order A x z →
    ¬ le-Cotransitive-Strict-Order A x y →
    le-Cotransitive-Strict-Order A y z
  right-le-left-nle-Cotransitive-Strict-Order =
    right-le-left-nle-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  left-le-right-nle-Cotransitive-Strict-Order :
    (x y z : type-Cotransitive-Strict-Order A) →
    le-Cotransitive-Strict-Order A x z →
    ¬ le-Cotransitive-Strict-Order A y z →
    le-Cotransitive-Strict-Order A x y
  left-le-right-nle-Cotransitive-Strict-Order =
    left-le-right-nle-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)
```

### Cotransitive strict orders have extensional incomparability

```agda
module _
  {l1 l2 : Level}
  (A : Cotransitive-Strict-Order l1 l2)
  where abstract

  eq-incomparable-Cotransitive-Strict-Order :
    (x y : type-Cotransitive-Strict-Order A) →
    ¬ le-Cotransitive-Strict-Order A x y →
    ¬ le-Cotransitive-Strict-Order A y x →
    x ＝ y
  eq-incomparable-Cotransitive-Strict-Order x y x≮y y≮x =
    extensionality-Cotransitive-Strict-Order A x y
      ( ( λ u →
          ( ( λ u<x →
              left-le-right-nle-Cotransitive-Strict-Order A u y x u<x y≮x) ,
            ( λ u<y →
              left-le-right-nle-Cotransitive-Strict-Order A u x y u<y x≮y))) ,
        ( λ u →
          ( ( λ x<u →
              right-le-left-nle-Cotransitive-Strict-Order A x y u x<u x≮y) ,
            ( λ y<u →
              right-le-left-nle-Cotransitive-Strict-Order A y x u y<u y≮x))))

  has-double-negation-stable-equality-Cotransitive-Strict-Order :
    has-double-negation-stable-equality (type-Cotransitive-Strict-Order A)
  has-double-negation-stable-equality-Cotransitive-Strict-Order =
    has-double-negation-stable-equality-eq-incomparable-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Order A)
      ( eq-incomparable-Cotransitive-Strict-Order)
```

### Comparability on cotransitive strict orders is a tight apartness relation

```agda
module _
  {l1 l2 : Level}
  (A : Cotransitive-Strict-Order l1 l2)
  where

  comparable-prop-Cotransitive-Strict-Order :
    Relation-Prop l2 (type-Cotransitive-Strict-Order A)
  comparable-prop-Cotransitive-Strict-Order =
    comparable-prop-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  comparable-Cotransitive-Strict-Order :
    Relation l2 (type-Cotransitive-Strict-Order A)
  comparable-Cotransitive-Strict-Order =
    comparable-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  is-antireflexive-comparable-Cotransitive-Strict-Order :
    is-antireflexive comparable-prop-Cotransitive-Strict-Order
  is-antireflexive-comparable-Cotransitive-Strict-Order =
    is-antireflexive-comparable-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  is-symmetric-comparable-Cotransitive-Strict-Order :
    is-symmetric comparable-Cotransitive-Strict-Order
  is-symmetric-comparable-Cotransitive-Strict-Order =
    is-symmetric-comparable-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  is-cotransitive-comparable-Cotransitive-Strict-Order :
    is-cotransitive comparable-prop-Cotransitive-Strict-Order
  is-cotransitive-comparable-Cotransitive-Strict-Order =
    is-cotransitive-comparable-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  is-apartness-relation-comparable-Cotransitive-Strict-Order :
    is-apartness-relation comparable-prop-Cotransitive-Strict-Order
  is-apartness-relation-comparable-Cotransitive-Strict-Order =
    is-apartness-relation-comparable-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  apartness-relation-comparable-Cotransitive-Strict-Order :
    Apartness-Relation l2 (type-Cotransitive-Strict-Order A)
  apartness-relation-comparable-Cotransitive-Strict-Order =
    apartness-relation-comparable-Cotransitive-Strict-Preorder
      ( cotransitive-strict-preorder-Cotransitive-Strict-Order A)

  is-tight-apartness-relation-comparable-Cotransitive-Strict-Order :
    is-tight-Apartness-Relation
      apartness-relation-comparable-Cotransitive-Strict-Order
  is-tight-apartness-relation-comparable-Cotransitive-Strict-Order x y nxy =
    eq-incomparable-Cotransitive-Strict-Order A x y
      ( λ x<y → nxy (inl-disjunction x<y))
      ( λ y<x → nxy (inr-disjunction y<x))

  tight-apartness-relation-comparable-Cotransitive-Strict-Order :
    Tight-Apartness-Relation l2 (type-Cotransitive-Strict-Order A)
  tight-apartness-relation-comparable-Cotransitive-Strict-Order =
    ( apartness-relation-comparable-Cotransitive-Strict-Order ,
      is-tight-apartness-relation-comparable-Cotransitive-Strict-Order)
```

### Cotransitive double negation stable strict orders satisfy weak trichotomy

```agda
module _
  {l1 l2 : Level}
  (A : Cotransitive-Strict-Order l1 l2)
  (dle-A :
    has-double-negation-stable-le-Strict-Order
      ( strict-order-Cotransitive-Strict-Order A))
  where

  ge-neq-nle-cotransitive-has-double-negation-stable-le-Strict-Order :
    (x y : type-Cotransitive-Strict-Order A) →
    ¬ le-Cotransitive-Strict-Order A x y →
    ¬ (x ＝ y) →
    le-Cotransitive-Strict-Order A y x
  ge-neq-nle-cotransitive-has-double-negation-stable-le-Strict-Order =
    ge-neq-nle-eq-incomparable-Double-Negation-Stable-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Order A , dle-A)
      ( eq-incomparable-Cotransitive-Strict-Order A)
```
