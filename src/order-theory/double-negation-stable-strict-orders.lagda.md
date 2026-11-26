# Double negation stable strict orders

```agda
module order-theory.double-negation-stable-strict-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-equality
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.double-negation-stable-strict-preorders
open import order-theory.strict-orders
open import order-theory.strict-preorders
```

</details>

## Idea

A [strict order](order-theory.strict-orders.md) is
{{#concept "double negation stable" Agda=has-double-negation-stable-le-Strict-Order Agda=Double-Negation-Stable-Strict-Order}}
if for all pairs of elements `x` and `y` the implication `¬¬ (x < y) ⇒ (x < y)`
holds.

## Definitions

### The predicate on strict orders

```agda
has-double-negation-stable-le-Strict-Order :
  {l1 l2 : Level} → Strict-Order l1 l2 → UU (l1 ⊔ l2)
has-double-negation-stable-le-Strict-Order A =
  has-double-negation-stable-le-Strict-Preorder
    ( strict-preorder-Strict-Order A)
```

### The type of double negation stable strict orders

```agda
Double-Negation-Stable-Strict-Order :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Double-Negation-Stable-Strict-Order l1 l2 =
  Σ (Strict-Order l1 l2) has-double-negation-stable-le-Strict-Order

module _
  {l1 l2 : Level} (A : Double-Negation-Stable-Strict-Order l1 l2)
  where

  strict-order-Double-Negation-Stable-Strict-Order : Strict-Order l1 l2
  strict-order-Double-Negation-Stable-Strict-Order = pr1 A

  strict-preorder-Double-Negation-Stable-Strict-Order : Strict-Preorder l1 l2
  strict-preorder-Double-Negation-Stable-Strict-Order =
    strict-preorder-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  extensionality-Double-Negation-Stable-Strict-Order :
    extensionality-principle-Strict-Preorder
      strict-preorder-Double-Negation-Stable-Strict-Order
  extensionality-Double-Negation-Stable-Strict-Order =
    extensionality-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  type-Double-Negation-Stable-Strict-Order : UU l1
  type-Double-Negation-Stable-Strict-Order =
    type-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  le-prop-Double-Negation-Stable-Strict-Order :
    Relation-Prop l2 type-Double-Negation-Stable-Strict-Order
  le-prop-Double-Negation-Stable-Strict-Order =
    le-prop-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  le-Double-Negation-Stable-Strict-Order :
    Relation l2 type-Double-Negation-Stable-Strict-Order
  le-Double-Negation-Stable-Strict-Order =
    le-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  is-prop-le-Double-Negation-Stable-Strict-Order :
    (x y : type-Double-Negation-Stable-Strict-Order) →
    is-prop (le-Double-Negation-Stable-Strict-Order x y)
  is-prop-le-Double-Negation-Stable-Strict-Order =
    is-prop-le-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  is-irreflexive-le-Double-Negation-Stable-Strict-Order :
    is-irreflexive le-Double-Negation-Stable-Strict-Order
  is-irreflexive-le-Double-Negation-Stable-Strict-Order =
    is-irreflexive-le-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  is-transitive-le-Double-Negation-Stable-Strict-Order :
    is-transitive le-Double-Negation-Stable-Strict-Order
  is-transitive-le-Double-Negation-Stable-Strict-Order =
    is-transitive-le-Strict-Order
      ( strict-order-Double-Negation-Stable-Strict-Order)

  has-double-negation-stable-le-Double-Negation-Stable-Strict-Order :
    has-double-negation-stable-le-Strict-Order
      strict-order-Double-Negation-Stable-Strict-Order
  has-double-negation-stable-le-Double-Negation-Stable-Strict-Order =
    pr2 A
```

## Properties

### Weak trichotomy gives double negation stable strict inequality

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Order l1 l2)
  (ge-neq-nle-A :
    (x y : type-Strict-Order A) →
    ¬ le-Strict-Order A x y →
    ¬ (x ＝ y) →
    le-Strict-Order A y x)
  where

  has-double-negation-stable-le-ge-neq-nle-Strict-Order :
    has-double-negation-stable-le-Strict-Order A
  has-double-negation-stable-le-ge-neq-nle-Strict-Order =
    has-double-negation-stable-le-ge-neq-nle-Strict-Preorder
      ( strict-preorder-Strict-Order A)
      ( ge-neq-nle-A)
```

### Weak trichotomy and double negation stable equality gives extensionality

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Preorder l1 l2)
  (ge-neq-nle-A :
    (x y : type-Strict-Preorder A) →
    ¬ le-Strict-Preorder A x y →
    ¬ (x ＝ y) →
    le-Strict-Preorder A y x)
  (dneq-A : has-double-negation-stable-equality (type-Strict-Preorder A))
  where

  ge-neq-nle-extensionality-Strict-Preorder :
    extensionality-principle-Strict-Preorder A
  ge-neq-nle-extensionality-Strict-Preorder =
    extensionality-eq-incomparable-Strict-Preorder A
      ( ge-neq-nle-eq-incomparable-Strict-Preorder A ge-neq-nle-A dneq-A)
```

### Double negation stable strict orders have double negation stable equality

```agda
module _
  {l1 l2 : Level}
  (A : Double-Negation-Stable-Strict-Order l1 l2)
  where

  iff-family-nneq-Double-Negation-Stable-Strict-Order :
    (B : type-Double-Negation-Stable-Strict-Order A → UU l2) →
    (dB : (t : type-Double-Negation-Stable-Strict-Order A) → ¬¬ B t → B t) →
    {x y : type-Double-Negation-Stable-Strict-Order A} →
    ¬¬ (x ＝ y) →
    (B x ↔ B y)
  iff-family-nneq-Double-Negation-Stable-Strict-Order B dB {x} {y} nneq =
    ( ( λ bx → dB y (λ nBy → nneq (λ p → nBy (tr B p bx)))) ,
      ( λ by → dB x (λ nBx → nneq (λ p → nBx (inv-tr B p by)))))

  has-double-negation-stable-equality-Double-Negation-Stable-Strict-Order :
    has-double-negation-stable-equality
      (type-Double-Negation-Stable-Strict-Order A)
  has-double-negation-stable-equality-Double-Negation-Stable-Strict-Order
    x y nneq =
    extensionality-Double-Negation-Stable-Strict-Order A x y
      ( ( λ u →
          iff-family-nneq-Double-Negation-Stable-Strict-Order
            ( λ t → le-Double-Negation-Stable-Strict-Order A u t)
            ( λ t →
              has-double-negation-stable-le-Double-Negation-Stable-Strict-Order
                ( A)
                ( u)
                ( t))
            ( nneq)) ,
        ( λ u →
          iff-family-nneq-Double-Negation-Stable-Strict-Order
            ( λ t → le-Double-Negation-Stable-Strict-Order A t u)
            ( λ t →
              has-double-negation-stable-le-Double-Negation-Stable-Strict-Order
                ( A)
                ( t)
                ( u))
            ( nneq)))
```
