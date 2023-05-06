# Join-semilattices

```agda
module order-theory.join-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
```

</details>

## Idea

A **join-semilattice** is a poset in which every pair of elements has a least
binary upper bound.

## Definitions

### Order theoretic join-semilattices

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-join-semilattice-Poset-Prop : Prop (l1 ⊔ l2)
  is-join-semilattice-Poset-Prop =
    Π-Prop
      ( type-Poset P)
      ( λ x →
        Π-Prop
          ( type-Poset P)
          ( has-least-binary-upper-bound-Poset-Prop P x))

  is-join-semilattice-Poset : UU (l1 ⊔ l2)
  is-join-semilattice-Poset = type-Prop is-join-semilattice-Poset-Prop

  is-prop-is-join-semilattice-Poset :
    is-prop is-join-semilattice-Poset
  is-prop-is-join-semilattice-Poset =
    is-prop-type-Prop is-join-semilattice-Poset-Prop

Join-Semilattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Join-Semilattice l1 l2 = Σ (Poset l1 l2) is-join-semilattice-Poset

module _
  {l1 l2 : Level} (A : Join-Semilattice l1 l2)
  where

  poset-Join-Semilattice : Poset l1 l2
  poset-Join-Semilattice = pr1 A

  type-Join-Semilattice : UU l1
  type-Join-Semilattice = type-Poset poset-Join-Semilattice

  leq-join-semilattice-Prop : (x y : type-Join-Semilattice) → Prop l2
  leq-join-semilattice-Prop = leq-Poset-Prop poset-Join-Semilattice

  leq-Join-Semilattice : (x y : type-Join-Semilattice) → UU l2
  leq-Join-Semilattice = leq-Poset poset-Join-Semilattice

  is-prop-leq-Join-Semilattice :
    (x y : type-Join-Semilattice) → is-prop (leq-Join-Semilattice x y)
  is-prop-leq-Join-Semilattice = is-prop-leq-Poset poset-Join-Semilattice

  refl-leq-Join-Semilattice :
    (x : type-Join-Semilattice) → leq-Join-Semilattice x x
  refl-leq-Join-Semilattice = refl-leq-Poset poset-Join-Semilattice

  antisymmetric-leq-Join-Semilattice :
    (x y : type-Join-Semilattice) →
    leq-Join-Semilattice x y → leq-Join-Semilattice y x → Id x y
  antisymmetric-leq-Join-Semilattice =
    antisymmetric-leq-Poset poset-Join-Semilattice

  transitive-leq-Join-Semilattice :
    (x y z : type-Join-Semilattice) →
    leq-Join-Semilattice y z → leq-Join-Semilattice x y →
    leq-Join-Semilattice x z
  transitive-leq-Join-Semilattice = transitive-leq-Poset poset-Join-Semilattice

  is-set-type-Join-Semilattice : is-set type-Join-Semilattice
  is-set-type-Join-Semilattice = is-set-type-Poset poset-Join-Semilattice

  set-Join-Semilattice : Set l1
  set-Join-Semilattice = set-Poset poset-Join-Semilattice

  is-join-semilattice-Join-Semilattice :
    is-join-semilattice-Poset poset-Join-Semilattice
  is-join-semilattice-Join-Semilattice = pr2 A

  join-semilattice-Join-Semilattice : Join-Semilattice l1 l2
  pr1 join-semilattice-Join-Semilattice = poset-Join-Semilattice
  pr2 join-semilattice-Join-Semilattice = is-join-semilattice-Join-Semilattice

  join-Join-Semilattice :
    (x y : type-Join-Semilattice) → type-Join-Semilattice
  join-Join-Semilattice x y =
    pr1 (is-join-semilattice-Join-Semilattice x y)

  is-least-binary-upper-bound-join-Join-Semilattice :
    (x y : type-Join-Semilattice) →
    is-least-binary-upper-bound-Poset poset-Join-Semilattice x y
      ( join-Join-Semilattice x y)
  is-least-binary-upper-bound-join-Join-Semilattice x y =
    pr2 (is-join-semilattice-Join-Semilattice x y)
```

### Algebraic join-semilattices

```agda
Algebraic-Join-Semilattice : (l : Level) → UU (lsuc l)
Algebraic-Join-Semilattice l =
  Σ ( Semigroup l)
    ( λ X →
      ( (x y : type-Semigroup X) →
        Id (mul-Semigroup X x y) (mul-Semigroup X y x)) ×
      ( (x : type-Semigroup X) → Id (mul-Semigroup X x x) x))
```
