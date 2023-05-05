# Finite posets

```agda
module order-theory.finite-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.finite-preorders
open import order-theory.posets

open import univalent-combinatorics.finite-types
```

</details>

## Definitions

A **finite poset** is a poset of which the underlying type is finite, and of
which the ordering relation is decidable.

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-finite-Poset-Prop : Prop (l1 ⊔ l2)
  is-finite-Poset-Prop = is-finite-Preorder-Prop (preorder-Poset P)

  is-finite-Poset : UU (l1 ⊔ l2)
  is-finite-Poset = is-finite-Preorder (preorder-Poset P)

  is-prop-is-finite-Poset : is-prop is-finite-Poset
  is-prop-is-finite-Poset = is-prop-is-finite-Preorder (preorder-Poset P)

  is-finite-type-is-finite-Poset :
    is-finite-Poset → is-finite (type-Poset P)
  is-finite-type-is-finite-Poset =
    is-finite-type-is-finite-Preorder (preorder-Poset P)

  is-decidable-leq-is-finite-Poset :
    is-finite-Poset →
    (x y : type-Poset P) → is-decidable (leq-Poset P x y)
  is-decidable-leq-is-finite-Poset =
    is-decidable-leq-is-finite-Preorder (preorder-Poset P)

Poset-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Poset-𝔽 l1 l2 =
  Σ ( Preorder-𝔽 l1 l2)
    ( λ P → is-antisymmetric-leq-Preorder (preorder-Preorder-𝔽 P))
```
