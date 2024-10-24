# Total orders

```agda
module order-theory.total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-preorders
```

</details>

## Idea

A **total order**, or a **linear order**, is a [poset](order-theory.posets.md)
`P` such that for every two elements `x` and `y` in `P` the
[disjunction](foundation.disjunction.md) `(x ≤ y) ∨ (y ≤ x)` holds. In other
words, total orders are totally ordered in the sense that any two elements are
comparable.

## Definitions

### Being a totally ordered poset

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  incident-Poset-Prop : (x y : type-Poset X) → Prop l2
  incident-Poset-Prop = incident-Preorder-Prop (preorder-Poset X)

  incident-Poset : (x y : type-Poset X) → UU l2
  incident-Poset = incident-Preorder (preorder-Poset X)

  is-prop-incident-Poset :
    (x y : type-Poset X) → is-prop (incident-Poset x y)
  is-prop-incident-Poset = is-prop-incident-Preorder (preorder-Poset X)

  is-total-Poset-Prop : Prop (l1 ⊔ l2)
  is-total-Poset-Prop = is-total-Preorder-Prop (preorder-Poset X)

  is-total-Poset : UU (l1 ⊔ l2)
  is-total-Poset = is-total-Preorder (preorder-Poset X)

  is-prop-is-total-Poset : is-prop is-total-Poset
  is-prop-is-total-Poset = is-prop-is-total-Preorder (preorder-Poset X)
```

### The type of total orders

```agda
Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Total-Order l1 l2 = Σ (Poset l1 l2) is-total-Poset

module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  poset-Total-Order : Poset l1 l2
  poset-Total-Order = pr1 X

  preorder-Total-Order : Preorder l1 l2
  preorder-Total-Order = preorder-Poset poset-Total-Order

  is-total-Total-Order : is-total-Poset (poset-Total-Order)
  is-total-Total-Order = pr2 X

  type-Total-Order : UU l1
  type-Total-Order = type-Poset poset-Total-Order

  leq-Total-Order-Prop : (x y : type-Total-Order) → Prop l2
  leq-Total-Order-Prop = leq-prop-Poset poset-Total-Order

  leq-Total-Order : (x y : type-Total-Order) → UU l2
  leq-Total-Order = leq-Poset poset-Total-Order

  is-prop-leq-Total-Order :
    (x y : type-Total-Order) → is-prop (leq-Total-Order x y)
  is-prop-leq-Total-Order = is-prop-leq-Poset poset-Total-Order

  concatenate-eq-leq-Total-Order :
    {x y z : type-Total-Order} → x ＝ y →
    leq-Total-Order y z → leq-Total-Order x z
  concatenate-eq-leq-Total-Order = concatenate-eq-leq-Poset poset-Total-Order

  concatenate-leq-eq-Total-Order :
    {x y z : type-Total-Order} →
    leq-Total-Order x y → y ＝ z → leq-Total-Order x z
  concatenate-leq-eq-Total-Order = concatenate-leq-eq-Poset poset-Total-Order

  refl-leq-Total-Order : is-reflexive leq-Total-Order
  refl-leq-Total-Order = refl-leq-Poset poset-Total-Order

  transitive-leq-Total-Order : is-transitive leq-Total-Order
  transitive-leq-Total-Order = transitive-leq-Poset poset-Total-Order

  antisymmetric-leq-Total-Order : is-antisymmetric leq-Total-Order
  antisymmetric-leq-Total-Order = antisymmetric-leq-Poset poset-Total-Order

  is-set-type-Total-Order : is-set type-Total-Order
  is-set-type-Total-Order = is-set-type-Poset poset-Total-Order

  set-Total-Order : Set l1
  set-Total-Order = set-Poset poset-Total-Order
```
