# Finite posets

```agda
module order-theory.finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.finite-preorders
open import order-theory.posets

open import univalent-combinatorics.finite-types
```

</details>

## Finite Posets

We say that a poset is finite if its underlying preorder is finite.

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-finite-poset-Prop : Prop (l1 ⊔ l2)
  is-finite-poset-Prop = is-finite-preorder-Prop (preorder-Poset X)

  is-finite-Poset : UU (l1 ⊔ l2)
  is-finite-Poset = is-finite-Preorder (preorder-Poset X)

  is-prop-is-finite-Poset : is-prop is-finite-Poset
  is-prop-is-finite-Poset = is-prop-is-finite-Preorder (preorder-Poset X)

  is-finite-element-is-finite-Poset :
    is-finite-Poset → is-finite (element-Poset X)
  is-finite-element-is-finite-Poset =
    is-finite-element-is-finite-Preorder (preorder-Poset X)

  is-decidable-leq-is-finite-Poset :
    is-finite-Poset →
    (x y : element-Poset X) → is-decidable (leq-Poset X x y)
  is-decidable-leq-is-finite-Poset =
    is-decidable-leq-is-finite-Preorder (preorder-Poset X)
```
