# Closed intervals in large posets

```agda
module order-theory.closed-intervals-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
```

</details>

## Idea

A
{{#concept "closed interval" disambiguation="in a large poset" Agda=closed-interval-Large-Poset}}
in a [large poset](order-theory.large-posets.md) `P` is a pair `x`, `y` at some
[universe level](foundation.universe-levels.md) with `x ≤ y` in `P`, and the
associated [subtype](foundation.subtypes.md) at each universe level of `P` of
elements `z` such that `x ≤ z ∧ z ≤ y`. Note, in particular, that we thus
consider closed intervals to be inhabited by convention.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  closed-interval-Large-Poset : (l1 l2 : Level) → UU (α l1 ⊔ α l2 ⊔ β l1 l2)
  closed-interval-Large-Poset l1 l2 =
    Σ ( type-Large-Poset P l1 × type-Large-Poset P l2)
      ( λ (x , y) → leq-Large-Poset P x y)

  is-in-closed-interval-prop-Large-Poset :
    {l1 l2 l3 : Level} → closed-interval-Large-Poset l1 l2 →
    type-Large-Poset P l3 → Prop (β l1 l3 ⊔ β l3 l2)
  is-in-closed-interval-prop-Large-Poset ((a , b) , _) x =
    leq-prop-Large-Poset P a x ∧ leq-prop-Large-Poset P x b

  is-in-closed-interval-Large-Poset :
    {l1 l2 l3 : Level} → closed-interval-Large-Poset l1 l2 →
    type-Large-Poset P l3 → UU (β l1 l3 ⊔ β l3 l2)
  is-in-closed-interval-Large-Poset [a,b] x =
    type-Prop (is-in-closed-interval-prop-Large-Poset [a,b] x)

  subtype-closed-interval-Large-Poset :
    {l1 l2 : Level} (l3 : Level) → closed-interval-Large-Poset l1 l2 →
    subtype (β l1 l3 ⊔ β l3 l2) (type-Large-Poset P l3)
  subtype-closed-interval-Large-Poset _ [a,b] =
    is-in-closed-interval-prop-Large-Poset [a,b]

  lower-bound-closed-interval-Large-Poset :
    {l1 l2 : Level} → closed-interval-Large-Poset l1 l2 → type-Large-Poset P l1
  lower-bound-closed-interval-Large-Poset ((a , b) , _) = a

  upper-bound-closed-interval-Large-Poset :
    {l1 l2 : Level} → closed-interval-Large-Poset l1 l2 → type-Large-Poset P l2
  upper-bound-closed-interval-Large-Poset ((a , b) , _) = b
```
