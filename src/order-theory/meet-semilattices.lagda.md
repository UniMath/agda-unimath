# Meet-semilattices

```agda
{-# OPTIONS --without-K --exact-split #-}

module order-theory.meet-semilattices where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using
  ( Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.sets using (is-set; Set)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import group-theory.semigroups using
  ( Semigroup; type-Semigroup; mul-Semigroup)

open import order-theory.greatest-lower-bounds-posets using
  ( has-greatest-binary-lower-bound-poset-Prop;
    is-greatest-binary-lower-bound-Poset)
open import order-theory.posets using
  ( Poset; element-Poset; leq-poset-Prop; leq-Poset; is-prop-leq-Poset;
    refl-leq-Poset; antisymmetric-leq-Poset; transitive-leq-Poset;
    is-set-element-Poset; element-poset-Set)
```

## Idea

A meet-semilattice is a poset in which every pair of elements has a greatest binary-lower bound.

## Definitions

### Order theoretic meet-semilattices

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-meet-semilattice-poset-Prop : Prop (l1 ⊔ l2)
  is-meet-semilattice-poset-Prop =
    Π-Prop
      ( element-Poset P)
      ( λ x →
        Π-Prop
          ( element-Poset P)
          ( has-greatest-binary-lower-bound-poset-Prop P x))

  is-meet-semilattice-Poset : UU (l1 ⊔ l2)
  is-meet-semilattice-Poset = type-Prop is-meet-semilattice-poset-Prop

  is-prop-is-meet-semilattice-Poset :
    is-prop is-meet-semilattice-Poset
  is-prop-is-meet-semilattice-Poset =
    is-prop-type-Prop is-meet-semilattice-poset-Prop

Meet-Semilattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Meet-Semilattice l1 l2 = Σ (Poset l1 l2) is-meet-semilattice-Poset

module _
  {l1 l2 : Level} (A : Meet-Semilattice l1 l2)
  where

  poset-Meet-Semilattice : Poset l1 l2
  poset-Meet-Semilattice = pr1 A

  element-Meet-Semilattice : UU l1
  element-Meet-Semilattice = element-Poset poset-Meet-Semilattice

  leq-meet-semilattice-Prop : (x y : element-Meet-Semilattice) → Prop l2
  leq-meet-semilattice-Prop = leq-poset-Prop poset-Meet-Semilattice

  leq-Meet-Semilattice : (x y : element-Meet-Semilattice) → UU l2
  leq-Meet-Semilattice = leq-Poset poset-Meet-Semilattice

  is-prop-leq-Meet-Semilattice :
    (x y : element-Meet-Semilattice) → is-prop (leq-Meet-Semilattice x y)
  is-prop-leq-Meet-Semilattice = is-prop-leq-Poset poset-Meet-Semilattice

  refl-leq-Meet-Semilattice :
    (x : element-Meet-Semilattice) → leq-Meet-Semilattice x x
  refl-leq-Meet-Semilattice = refl-leq-Poset poset-Meet-Semilattice

  antisymmetric-leq-Meet-Semilattice :
    (x y : element-Meet-Semilattice) →
    leq-Meet-Semilattice x y → leq-Meet-Semilattice y x → Id x y
  antisymmetric-leq-Meet-Semilattice =
    antisymmetric-leq-Poset poset-Meet-Semilattice

  transitive-leq-Meet-Semilattice :
    (x y z : element-Meet-Semilattice) →
    leq-Meet-Semilattice y z → leq-Meet-Semilattice x y →
    leq-Meet-Semilattice x z
  transitive-leq-Meet-Semilattice = transitive-leq-Poset poset-Meet-Semilattice

  is-set-element-Meet-Semilattice : is-set element-Meet-Semilattice
  is-set-element-Meet-Semilattice = is-set-element-Poset poset-Meet-Semilattice

  element-meet-semilattice-Set : Set l1
  element-meet-semilattice-Set = element-poset-Set poset-Meet-Semilattice

  is-meet-semilattice-Meet-Semilattice :
    is-meet-semilattice-Poset poset-Meet-Semilattice
  is-meet-semilattice-Meet-Semilattice = pr2 A

  meet-semilattice-Meet-Semilattice : Meet-Semilattice l1 l2
  pr1 meet-semilattice-Meet-Semilattice = poset-Meet-Semilattice
  pr2 meet-semilattice-Meet-Semilattice = is-meet-semilattice-Meet-Semilattice

  meet-Meet-Semilattice :
    (x y : element-Meet-Semilattice) → element-Meet-Semilattice
  meet-Meet-Semilattice x y =
    pr1 (is-meet-semilattice-Meet-Semilattice x y)

  is-greatest-binary-lower-bound-meet-Meet-Semilattice :
    (x y : element-Meet-Semilattice) →
    is-greatest-binary-lower-bound-Poset poset-Meet-Semilattice x y
      ( meet-Meet-Semilattice x y)
  is-greatest-binary-lower-bound-meet-Meet-Semilattice x y =
    pr2 (is-meet-semilattice-Meet-Semilattice x y)
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
