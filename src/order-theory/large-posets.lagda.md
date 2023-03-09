# Large Posets

```agda
module order-theory.large-posets where
```

<details><summary>Imports</summary>

```agda
open import Agda.Primitive using (Setω)

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-preorders
open import order-theory.posets
```

</details>

## Idea

A large poset is a large preorder such that the restriction of the ordering relation to any particular universe level is antisymmetric

## Definition

```agda
record
  Large-Poset (α : Level → Level) (β : Level → Level → Level) : Setω where
  constructor
    make-Large-Poset
  field
    large-preorder-Large-Poset : Large-Preorder α β
    antisymmetric-leq-Large-Poset :
      {l : Level} (x y : type-Large-Preorder large-preorder-Large-Poset l) →
      leq-Large-Preorder large-preorder-Large-Poset x y →
      leq-Large-Preorder large-preorder-Large-Poset y x → Id x y

open Large-Poset public

module _
  {α : Level → Level} {β : Level → Level → Level} (X : Large-Poset α β)
  where

  type-Large-Poset : (l : Level) → UU (α l)
  type-Large-Poset = type-Large-Preorder (large-preorder-Large-Poset X)

  leq-large-poset-Prop :
    {l1 l2 : Level} → type-Large-Poset l1 → type-Large-Poset l2 →
    Prop (β l1 l2)
  leq-large-poset-Prop = leq-large-preorder-Prop (large-preorder-Large-Poset X)

  leq-Large-Poset :
    {l1 l2 : Level} → type-Large-Poset l1 → type-Large-Poset l2 → UU (β l1 l2)
  leq-Large-Poset = leq-Large-Preorder (large-preorder-Large-Poset X)

  is-prop-leq-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset l1) (y : type-Large-Poset l2) →
    is-prop (leq-Large-Poset x y)
  is-prop-leq-Large-Poset =
    is-prop-leq-Large-Preorder (large-preorder-Large-Poset X)

  refl-leq-Large-Poset :
    {l1 : Level} (x : type-Large-Poset l1) → leq-Large-Poset x x
  refl-leq-Large-Poset = refl-leq-Large-Preorder (large-preorder-Large-Poset X)

  trans-leq-Large-Poset :
    {l1 l2 l3 : Level} (x : type-Large-Poset l1) (y : type-Large-Poset l2)
    (z : type-Large-Poset l3) →
    leq-Large-Poset y z → leq-Large-Poset x y → leq-Large-Poset x z
  trans-leq-Large-Poset =
    trans-leq-Large-Preorder (large-preorder-Large-Poset X)

  poset-Large-Poset : (l : Level) → Poset (α l) (β l l)
  pr1 (poset-Large-Poset l) = type-Large-Poset l
  pr1 (pr2 (poset-Large-Poset l)) = leq-large-poset-Prop
  pr1 (pr1 (pr2 (pr2 (poset-Large-Poset l)))) = refl-leq-Large-Poset
  pr2 (pr1 (pr2 (pr2 (poset-Large-Poset l)))) = trans-leq-Large-Poset
  pr2 (pr2 (pr2 (poset-Large-Poset l))) = antisymmetric-leq-Large-Poset X
```
