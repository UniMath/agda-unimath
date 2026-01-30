# Total preorders

```agda
module order-theory.total-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.coproduct-types
open import foundation.functoriality-disjunction
open import foundation.propositions
open import foundation.apartness-relations
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **total preorder** is a preorder `P` such that for every two elements
`x y : P` the disjunction `(x ≤ y) ∨ (y ≤ x)` holds. In other words, total
preorders are totally ordered in the sense that any two elements can be
compared.

## Definition

### Being a total preorder

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  incident-Preorder-Prop : (x y : type-Preorder X) → Prop l2
  incident-Preorder-Prop x y =
    (leq-prop-Preorder X x y) ∨ (leq-prop-Preorder X y x)

  incident-Preorder : (x y : type-Preorder X) → UU l2
  incident-Preorder x y = type-Prop (incident-Preorder-Prop x y)

  is-prop-incident-Preorder :
    (x y : type-Preorder X) → is-prop (incident-Preorder x y)
  is-prop-incident-Preorder x y = is-prop-type-Prop (incident-Preorder-Prop x y)

  is-total-prop-Preorder : Prop (l1 ⊔ l2)
  is-total-prop-Preorder =
    Π-Prop
      ( type-Preorder X)
      ( λ x → Π-Prop ( type-Preorder X) (λ y → incident-Preorder-Prop x y))

  is-total-Preorder : UU (l1 ⊔ l2)
  is-total-Preorder = type-Prop is-total-prop-Preorder

  is-prop-is-total-Preorder : is-prop is-total-Preorder
  is-prop-is-total-Preorder = is-prop-type-Prop is-total-prop-Preorder
```

### The type of total preorder

```agda
Total-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Total-Preorder l1 l2 = Σ (Preorder l1 l2) is-total-Preorder

module _
  {l1 l2 : Level} (X : Total-Preorder l1 l2)
  where

  preorder-Total-Preorder : Preorder l1 l2
  preorder-Total-Preorder = pr1 X

  is-total-Total-Preorder : is-total-Preorder preorder-Total-Preorder
  is-total-Total-Preorder = pr2 X

  type-Total-Preorder : UU l1
  type-Total-Preorder = type-Preorder preorder-Total-Preorder

  leq-prop-Total-Preorder : (x y : type-Total-Preorder) → Prop l2
  leq-prop-Total-Preorder = leq-prop-Preorder preorder-Total-Preorder

  leq-Total-Preorder : (x y : type-Total-Preorder) → UU l2
  leq-Total-Preorder = leq-Preorder preorder-Total-Preorder

  is-prop-leq-Total-Preorder :
    (x y : type-Total-Preorder) → is-prop (leq-Total-Preorder x y)
  is-prop-leq-Total-Preorder = is-prop-leq-Preorder preorder-Total-Preorder

  refl-leq-Total-Preorder : is-reflexive leq-Total-Preorder
  refl-leq-Total-Preorder = refl-leq-Preorder preorder-Total-Preorder

  transitive-leq-Total-Preorder : is-transitive leq-Total-Preorder
  transitive-leq-Total-Preorder =
    transitive-leq-Preorder preorder-Total-Preorder
```

## Properties

### Total preorders are cotransitive

```agda
module _
  {l1 l2 : Level} (X : Total-Preorder l1 l2)
  (let _≤_ = leq-Total-Preorder X)
  where

  is-cotransitive-leq-Total-Preorder :
    (x y z : type-Total-Preorder X) → x ≤ z → disjunction-type (x ≤ y) (y ≤ z)
  is-cotransitive-leq-Total-Preorder x y z x≤z =
    map-disjunction
      ( id)
      ( transitive-leq-Total-Preorder X y x z x≤z)
      ( is-total-Total-Preorder X x y)
```
