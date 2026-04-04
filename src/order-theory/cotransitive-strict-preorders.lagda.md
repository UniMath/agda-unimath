# Cotransitive strict preorders

```agda
module order-theory.cotransitive-strict-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation-stable-equality
open import foundation.empty-types
open import foundation.function-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.strict-orders
open import order-theory.strict-preorders
```

</details>

## Idea

A [strict preorder](order-theory.strict-preorders.md) is
{{#concept "cotransitive" Disambiguation="strict preorder" Agda=is-cotransitive-le-Strict-Preorder Agda=Cotransitive-Strict-Preorder}}
if whenever `x < z`, then for any `y`, either `x < y` or `y < z`.

## Definitions

### The predicate on strict preorders of being cotransitive

```agda
is-cotransitive-le-Strict-Preorder :
  {l1 l2 : Level} → Strict-Preorder l1 l2 → UU (l1 ⊔ l2)
is-cotransitive-le-Strict-Preorder A =
  (x y z : type-Strict-Preorder A) →
  le-Strict-Preorder A x z →
  disjunction-type (le-Strict-Preorder A x y) (le-Strict-Preorder A y z)
```

### The type of cotransitive strict preorders

```agda
Cotransitive-Strict-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Cotransitive-Strict-Preorder l1 l2 =
  Σ (Strict-Preorder l1 l2) is-cotransitive-le-Strict-Preorder

module _
  {l1 l2 : Level} (A : Cotransitive-Strict-Preorder l1 l2)
  where

  strict-preorder-Cotransitive-Strict-Preorder : Strict-Preorder l1 l2
  strict-preorder-Cotransitive-Strict-Preorder = pr1 A

  type-Cotransitive-Strict-Preorder : UU l1
  type-Cotransitive-Strict-Preorder =
    type-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Preorder)

  le-prop-Cotransitive-Strict-Preorder :
    Relation-Prop l2 type-Cotransitive-Strict-Preorder
  le-prop-Cotransitive-Strict-Preorder =
    le-prop-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Preorder)

  le-Cotransitive-Strict-Preorder :
    Relation l2 type-Cotransitive-Strict-Preorder
  le-Cotransitive-Strict-Preorder =
    le-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Preorder)

  is-prop-le-Cotransitive-Strict-Preorder :
    (x y : type-Cotransitive-Strict-Preorder) →
    is-prop (le-Cotransitive-Strict-Preorder x y)
  is-prop-le-Cotransitive-Strict-Preorder =
    is-prop-le-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Preorder)

  is-irreflexive-le-Cotransitive-Strict-Preorder :
    is-irreflexive le-Cotransitive-Strict-Preorder
  is-irreflexive-le-Cotransitive-Strict-Preorder =
    is-irreflexive-le-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Preorder)

  is-transitive-le-Cotransitive-Strict-Preorder :
    is-transitive le-Cotransitive-Strict-Preorder
  is-transitive-le-Cotransitive-Strict-Preorder =
    is-transitive-le-Strict-Preorder
      ( strict-preorder-Cotransitive-Strict-Preorder)

  is-cotransitive-le-Cotransitive-Strict-Preorder :
    is-cotransitive-le-Strict-Preorder
      strict-preorder-Cotransitive-Strict-Preorder
  is-cotransitive-le-Cotransitive-Strict-Preorder =
    pr2 A
```

## Properties

### Eliminating cotransitivity by negation

```agda
module _
  {l1 l2 : Level}
  (A : Cotransitive-Strict-Preorder l1 l2)
  where abstract

  right-le-left-nle-Cotransitive-Strict-Preorder :
    (x y z : type-Cotransitive-Strict-Preorder A) →
    le-Cotransitive-Strict-Preorder A x z →
    ¬ le-Cotransitive-Strict-Preorder A x y →
    le-Cotransitive-Strict-Preorder A y z
  right-le-left-nle-Cotransitive-Strict-Preorder x y z x<z x≮y =
    elim-disjunction
      ( le-prop-Cotransitive-Strict-Preorder A y z)
      ( λ x<y → ex-falso (x≮y x<y))
      ( id)
      ( is-cotransitive-le-Cotransitive-Strict-Preorder A x y z x<z)

  left-le-right-nle-Cotransitive-Strict-Preorder :
    (x y z : type-Cotransitive-Strict-Preorder A) →
    le-Cotransitive-Strict-Preorder A x z →
    ¬ le-Cotransitive-Strict-Preorder A y z →
    le-Cotransitive-Strict-Preorder A x y
  left-le-right-nle-Cotransitive-Strict-Preorder x y z x<z y≮z =
    elim-disjunction
      ( le-prop-Cotransitive-Strict-Preorder A x y)
      ( id)
      ( λ y<z → ex-falso (y≮z y<z))
      ( is-cotransitive-le-Cotransitive-Strict-Preorder A x y z x<z)
```

### Comparability on cotransitive strict preorders form an apartness relation

```agda
module _
  {l1 l2 : Level}
  (A : Cotransitive-Strict-Preorder l1 l2)
  where

  comparable-prop-Cotransitive-Strict-Preorder :
    Relation-Prop l2 (type-Cotransitive-Strict-Preorder A)
  comparable-prop-Cotransitive-Strict-Preorder x y =
    ( le-prop-Cotransitive-Strict-Preorder A x y) ∨
    ( le-prop-Cotransitive-Strict-Preorder A y x)

  comparable-Cotransitive-Strict-Preorder :
    Relation l2 (type-Cotransitive-Strict-Preorder A)
  comparable-Cotransitive-Strict-Preorder x y =
    type-Prop (comparable-prop-Cotransitive-Strict-Preorder x y)

  is-antireflexive-comparable-Cotransitive-Strict-Preorder :
    is-antireflexive comparable-prop-Cotransitive-Strict-Preorder
  is-antireflexive-comparable-Cotransitive-Strict-Preorder x =
    elim-disjunction
      ( empty-Prop)
      ( is-irreflexive-le-Cotransitive-Strict-Preorder A x)
      ( is-irreflexive-le-Cotransitive-Strict-Preorder A x)

  is-symmetric-comparable-Cotransitive-Strict-Preorder :
    is-symmetric comparable-Cotransitive-Strict-Preorder
  is-symmetric-comparable-Cotransitive-Strict-Preorder _ _ =
    swap-disjunction

  is-cotransitive-comparable-Cotransitive-Strict-Preorder :
    is-cotransitive comparable-prop-Cotransitive-Strict-Preorder
  is-cotransitive-comparable-Cotransitive-Strict-Preorder x y z =
    elim-disjunction
      ( disjunction-type-Prop
        ( comparable-Cotransitive-Strict-Preorder x y)
        ( comparable-Cotransitive-Strict-Preorder y z))
      ( λ x<z →
        elim-disjunction
          ( disjunction-type-Prop
            ( comparable-Cotransitive-Strict-Preorder x y)
            ( comparable-Cotransitive-Strict-Preorder y z))
          ( λ x<y → inl-disjunction (inl-disjunction x<y))
          ( λ y<z → inr-disjunction (inl-disjunction y<z))
          ( is-cotransitive-le-Cotransitive-Strict-Preorder A x y z x<z))
      ( λ z<x →
        elim-disjunction
          ( disjunction-type-Prop
            ( comparable-Cotransitive-Strict-Preorder x y)
            ( comparable-Cotransitive-Strict-Preorder y z))
          ( λ z<y → inr-disjunction (inr-disjunction z<y))
          ( λ y<x → inl-disjunction (inr-disjunction y<x))
          ( is-cotransitive-le-Cotransitive-Strict-Preorder A z y x z<x))

  is-apartness-relation-comparable-Cotransitive-Strict-Preorder :
    is-apartness-relation comparable-prop-Cotransitive-Strict-Preorder
  is-apartness-relation-comparable-Cotransitive-Strict-Preorder =
    ( is-antireflexive-comparable-Cotransitive-Strict-Preorder ,
      is-symmetric-comparable-Cotransitive-Strict-Preorder ,
      is-cotransitive-comparable-Cotransitive-Strict-Preorder)

  apartness-relation-comparable-Cotransitive-Strict-Preorder :
    Apartness-Relation l2 (type-Cotransitive-Strict-Preorder A)
  apartness-relation-comparable-Cotransitive-Strict-Preorder =
    ( comparable-prop-Cotransitive-Strict-Preorder ,
      is-apartness-relation-comparable-Cotransitive-Strict-Preorder)
```
