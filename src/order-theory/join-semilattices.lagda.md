# Join-semilattices

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.join-semilattices where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using
  ( UU-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import group-theory.semigroups using
  ( Semigroup; type-Semigroup; mul-Semigroup)

open import order-theory.least-upper-bounds-posets using
  ( has-least-upper-bound-poset-Prop)
open import order-theory.posets using (Poset; element-Poset)
```

## Idea

A join-semilattice is a poset in which every pair of elements has a least upper bound.

## Definitions

### Concrete meet-semilattices

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-meet-semilattice-poset-Prop : UU-Prop (l1 ⊔ l2)
  is-meet-semilattice-poset-Prop =
    Π-Prop
      ( element-Poset P)
      ( λ x →
        Π-Prop
          ( element-Poset P)
          ( has-least-upper-bound-poset-Prop P x))

  is-meet-semilattice-Poset : UU (l1 ⊔ l2)
  is-meet-semilattice-Poset = type-Prop is-meet-semilattice-poset-Prop

  is-prop-is-meet-semilattice-Poset :
    is-prop is-meet-semilattice-Poset
  is-prop-is-meet-semilattice-Poset =
    is-prop-type-Prop is-meet-semilattice-poset-Prop

Meet-Semilattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Meet-Semilattice l1 l2 = Σ (Poset l1 l2) is-meet-semilattice-Poset
```

### Algebraic meet-semilattices

```agda
Algebraic-Meet-Semilattice : (l : Level) → UU (lsuc l)
Algebraic-Meet-Semilattice l =
  Σ ( Semigroup l)
    ( λ X →
      ( (x y : type-Semigroup X) →
        Id (mul-Semigroup X x y) (mul-Semigroup X y x)) ×
      ( (x : type-Semigroup X) → Id (mul-Semigroup X x x) x))
```
