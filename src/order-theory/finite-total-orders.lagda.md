# Finite total orders

```agda
module order-theory.finite-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.finite-posets
open import order-theory.posets
open import order-theory.total-orders

open import univalent-combinatorics.finite-types
```

</details>

## Definitions

A **finite total order** is a [total order](order-theory.total-orders.md) of
which the underlying type is [finite](univalent-combinatorics.finite-types.md),
and of which the ordering relation is
[decidable](foundation.decidable-relations.md).

```agda
module _
  {l1 l2 : Level} (P : Total-Order l1 l2)
  where

  is-finite-Total-Order-Prop : Prop (l1 ⊔ l2)
  is-finite-Total-Order-Prop = is-finite-Poset-Prop (poset-Total-Order P)

  is-finite-Total-Order : UU (l1 ⊔ l2)
  is-finite-Total-Order = is-finite-Poset (poset-Total-Order P)

  is-prop-is-finite-Total-Order : is-prop is-finite-Total-Order
  is-prop-is-finite-Total-Order =
    is-prop-is-finite-Poset (poset-Total-Order P)

  is-finite-type-is-finite-Total-Order :
    is-finite-Total-Order → is-finite (type-Total-Order P)
  is-finite-type-is-finite-Total-Order =
    is-finite-type-is-finite-Poset (poset-Total-Order P)

  is-decidable-leq-is-finite-Total-Order :
    is-finite-Total-Order →
    (x y : type-Total-Order P) → is-decidable (leq-Total-Order P x y)
  is-decidable-leq-is-finite-Total-Order =
    is-decidable-leq-is-finite-Poset (poset-Total-Order P)

is-finite-total-order-Poset-Prop :
  {l1 l2 : Level} (P : Poset l1 l2) → Prop (l1 ⊔ l2)
is-finite-total-order-Poset-Prop P =
  product-Prop
    ( is-total-Poset-Prop P)
    ( is-finite-Poset-Prop P)

Total-Order-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Total-Order-𝔽 l1 l2 =
  Σ ( Finite-Poset l1 l2)
    ( λ P → is-total-Poset (poset-Finite-Poset P))

finite-poset-Total-Order-𝔽 : {l1 l2 : Level} → Total-Order-𝔽 l1 l2 → Finite-Poset l1 l2
finite-poset-Total-Order-𝔽 = pr1

poset-Total-Order-𝔽 : {l1 l2 : Level} → Total-Order-𝔽 l1 l2 → Poset l1 l2
poset-Total-Order-𝔽 = poset-Finite-Poset ∘ finite-poset-Total-Order-𝔽

is-total-Total-Order-𝔽 :
  {l1 l2 : Level} (P : Total-Order-𝔽 l1 l2) →
  is-total-Poset (poset-Total-Order-𝔽 P)
is-total-Total-Order-𝔽 = pr2

total-order-Total-Order-𝔽 :
  {l1 l2 : Level} → Total-Order-𝔽 l1 l2 → Total-Order l1 l2
pr1 (total-order-Total-Order-𝔽 P) = poset-Total-Order-𝔽 P
pr2 (total-order-Total-Order-𝔽 P) = is-total-Total-Order-𝔽 P

type-Total-Order-𝔽 :
  {l1 l2 : Level} → Total-Order-𝔽 l1 l2 → UU l1
type-Total-Order-𝔽 = type-Poset ∘ poset-Total-Order-𝔽
```
