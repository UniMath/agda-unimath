# Infinite distributive law

```agda
module order-theory.infinite-distributive-law where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

Let A be a poset that has all binary meets and arbitrary joins (which we call
sups). We can show that all sup lattices have binary meets (and we plan to in
another file), but this economy offers little benefit here. The infinite
distributive law states: for all `a : A` and for all families `b : I → A` the
following identity holds: `a ∧ (‌‌‌⋁ᵢ bᵢ) ＝ ⋁ᵢ (a ∧ bᵢ)`.

Note: One could inquire about the dual infinite distributive law but it is not
needed at this time.

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-meet-suplattice-Poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-meet-suplattice-Poset-Prop =
    prod-Prop
      ( is-meet-semilattice-Poset-Prop P)
      ( is-suplattice-Poset-Prop l3 P)

  is-meet-suplattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-meet-suplattice-Poset = type-Prop is-meet-suplattice-Poset-Prop

  is-prop-is-meet-suplattice-Poset : is-prop is-meet-suplattice-Poset
  is-prop-is-meet-suplattice-Poset =
    is-prop-type-Prop is-meet-suplattice-Poset-Prop

Meet-Suplattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Meet-Suplattice l1 l2 l3 =
  Σ (Poset l1 l2) (is-meet-suplattice-Poset l3)
```

We need to provide the appropriate components to state the infinite distributive
law.

```agda
module _
  {l1 l2 l3 : Level} (A : Meet-Suplattice l1 l2 l3)
  where

  poset-Meet-Suplattice : Poset l1 l2
  poset-Meet-Suplattice = pr1 A

  element-Meet-Suplattice : UU l1
  element-Meet-Suplattice =
    element-Poset poset-Meet-Suplattice

  leq-meet-suplattice-Prop : (x y : element-Meet-Suplattice) → Prop l2
  leq-meet-suplattice-Prop = leq-Poset-Prop poset-Meet-Suplattice

  leq-Meet-Suplattice : (x y : element-Meet-Suplattice) → UU l2
  leq-Meet-Suplattice = leq-Poset poset-Meet-Suplattice

  is-prop-leq-Meet-Suplattice :
    (x y : element-Meet-Suplattice) → is-prop (leq-Meet-Suplattice x y)
  is-prop-leq-Meet-Suplattice = is-prop-leq-Poset poset-Meet-Suplattice

  refl-leq-Meet-Suplattice :
    (x : element-Meet-Suplattice) → leq-Meet-Suplattice x x
  refl-leq-Meet-Suplattice = refl-leq-Poset poset-Meet-Suplattice

  antisymmetric-leq-Meet-Suplattice :
    (x y : element-Meet-Suplattice) →
    leq-Meet-Suplattice x y → leq-Meet-Suplattice y x → x ＝ y
  antisymmetric-leq-Meet-Suplattice =
    antisymmetric-leq-Poset poset-Meet-Suplattice

  transitive-leq-Meet-Suplattice :
    (x y z : element-Meet-Suplattice) →
    leq-Meet-Suplattice y z → leq-Meet-Suplattice x y →
    leq-Meet-Suplattice x z
  transitive-leq-Meet-Suplattice = transitive-leq-Poset poset-Meet-Suplattice

  is-set-element-Meet-Suplattice : is-set element-Meet-Suplattice
  is-set-element-Meet-Suplattice = is-set-element-Poset poset-Meet-Suplattice

  set-Meet-Suplattice : Set l1
  set-Meet-Suplattice = set-Poset poset-Meet-Suplattice

  is-meet-semilattice-Meet-Suplattice :
    is-meet-semilattice-Poset poset-Meet-Suplattice
  is-meet-semilattice-Meet-Suplattice = pr1 (pr2 A)

  meet-semilattice-Meet-Suplattice : Meet-Semilattice l1 l2
  meet-semilattice-Meet-Suplattice =
    ( poset-Meet-Suplattice , is-meet-semilattice-Meet-Suplattice)

  is-suplattice-Meet-Suplattice :
    is-suplattice-Poset l3 poset-Meet-Suplattice
  is-suplattice-Meet-Suplattice = pr2 (pr2 A)

  suplattice-Meet-Suplattice : Suplattice l1 l2 l3
  suplattice-Meet-Suplattice =
    ( poset-Meet-Suplattice , is-suplattice-Meet-Suplattice)

  meet-suplattice-Meet-Suplattice :
    Meet-Suplattice l1 l2 l3
  pr1 meet-suplattice-Meet-Suplattice =
    poset-Meet-Suplattice
  pr1 (pr2 meet-suplattice-Meet-Suplattice) =
    is-meet-semilattice-Meet-Suplattice
  pr2 (pr2 meet-suplattice-Meet-Suplattice) =
    is-suplattice-Meet-Suplattice

  meet-Meet-Suplattice :
    (x y : element-Meet-Suplattice) →
    element-Meet-Suplattice
  meet-Meet-Suplattice x y = pr1 (is-meet-semilattice-Meet-Suplattice x y)

  sup-Meet-Suplattice :
    (I : UU l3) → (I → element-Meet-Suplattice) →
    element-Meet-Suplattice
  sup-Meet-Suplattice I f = pr1 (is-suplattice-Meet-Suplattice I f)
```

## Statement of the infinite distributive law

```agda
distributive-law-meet-suplattice :
  (l1 l2 l3 : Level) → (Meet-Suplattice l1 l2 l3) → UU (l1 ⊔ lsuc l3)
distributive-law-meet-suplattice l1 l2 l3 A =
  (a : element-Meet-Suplattice A) → {I : UU l3} →
  (b : I → element-Meet-Suplattice A) →
  (meet-Meet-Suplattice A a (sup-Meet-Suplattice A I b) ＝
  sup-Meet-Suplattice A I (λ i → (meet-Meet-Suplattice A a (b i))))
```

This notation is not easy on the eye, but recall, in more familiar notation the
identity expressed here is: `a ∧ (‌‌‌⋁ᵢ bᵢ) ＝ ⋁ᵢ (a ∧ bᵢ)`.
