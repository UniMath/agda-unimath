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
  {l1 : Level} (l2 : Level) (X : Meet-Semilattice l1)
  where

  is-meet-suplattice-Meet-Semilattice-Prop : Prop (l1 ⊔ lsuc l2)
  is-meet-suplattice-Meet-Semilattice-Prop =
    is-suplattice-Poset-Prop l2 (poset-Meet-Semilattice X)

  is-meet-suplattice-Meet-Semilattice : UU (l1 ⊔ lsuc l2)
  is-meet-suplattice-Meet-Semilattice =
    type-Prop is-meet-suplattice-Meet-Semilattice-Prop

  is-prop-is-meet-suplattice-Meet-Semilattice :
    is-prop is-meet-suplattice-Meet-Semilattice
  is-prop-is-meet-suplattice-Meet-Semilattice =
    is-prop-type-Prop is-meet-suplattice-Meet-Semilattice-Prop

Meet-Suplattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Meet-Suplattice l1 l2 =
  Σ (Meet-Semilattice l1) (is-meet-suplattice-Meet-Semilattice l2)
```

We need to provide the appropriate components to state the infinite distributive
law.

```agda
module _
  {l1 l2 : Level} (A : Meet-Suplattice l1 l2)
  where

  meet-semilattice-Meet-Suplattice : Meet-Semilattice l1
  meet-semilattice-Meet-Suplattice = pr1 A

  poset-Meet-Suplattice : Poset l1 l1
  poset-Meet-Suplattice =
    poset-Meet-Semilattice meet-semilattice-Meet-Suplattice

  type-Meet-Suplattice : UU l1
  type-Meet-Suplattice =
    type-Poset poset-Meet-Suplattice

  leq-meet-suplattice-Prop : (x y : type-Meet-Suplattice) → Prop l1
  leq-meet-suplattice-Prop = leq-Poset-Prop poset-Meet-Suplattice

  leq-Meet-Suplattice : (x y : type-Meet-Suplattice) → UU l1
  leq-Meet-Suplattice = leq-Poset poset-Meet-Suplattice

  is-prop-leq-Meet-Suplattice :
    (x y : type-Meet-Suplattice) → is-prop (leq-Meet-Suplattice x y)
  is-prop-leq-Meet-Suplattice = is-prop-leq-Poset poset-Meet-Suplattice

  refl-leq-Meet-Suplattice :
    (x : type-Meet-Suplattice) → leq-Meet-Suplattice x x
  refl-leq-Meet-Suplattice = refl-leq-Poset poset-Meet-Suplattice

  antisymmetric-leq-Meet-Suplattice :
    (x y : type-Meet-Suplattice) →
    leq-Meet-Suplattice x y → leq-Meet-Suplattice y x → x ＝ y
  antisymmetric-leq-Meet-Suplattice =
    antisymmetric-leq-Poset poset-Meet-Suplattice

  transitive-leq-Meet-Suplattice :
    (x y z : type-Meet-Suplattice) →
    leq-Meet-Suplattice y z → leq-Meet-Suplattice x y →
    leq-Meet-Suplattice x z
  transitive-leq-Meet-Suplattice = transitive-leq-Poset poset-Meet-Suplattice

  is-set-type-Meet-Suplattice : is-set type-Meet-Suplattice
  is-set-type-Meet-Suplattice = is-set-type-Poset poset-Meet-Suplattice

  set-Meet-Suplattice : Set l1
  set-Meet-Suplattice = set-Poset poset-Meet-Suplattice

  is-suplattice-Meet-Suplattice :
    is-suplattice-Poset l2 poset-Meet-Suplattice
  is-suplattice-Meet-Suplattice = pr2 A

  suplattice-Meet-Suplattice : Suplattice l1 l1 l2
  suplattice-Meet-Suplattice =
    ( poset-Meet-Suplattice , is-suplattice-Meet-Suplattice)

  meet-Meet-Suplattice :
    (x y : type-Meet-Suplattice) →
    type-Meet-Suplattice
  meet-Meet-Suplattice =
    meet-Meet-Semilattice meet-semilattice-Meet-Suplattice

  sup-Meet-Suplattice :
    (I : UU l2) → (I → type-Meet-Suplattice) →
    type-Meet-Suplattice
  sup-Meet-Suplattice I f = pr1 (is-suplattice-Meet-Suplattice I f)
```

## Statement of the infinite distributive law

```agda
distributive-law-meet-suplattice :
  (l1 l2 : Level) → (Meet-Suplattice l1 l2) → UU (l1 ⊔ lsuc l2)
distributive-law-meet-suplattice l1 l2 A =
  (a : type-Meet-Suplattice A) → {I : UU l2} →
  (b : I → type-Meet-Suplattice A) →
  (meet-Meet-Suplattice A a (sup-Meet-Suplattice A I b) ＝
  sup-Meet-Suplattice A I (λ i → (meet-Meet-Suplattice A a (b i))))
```

This notation is not easy on the eye, but recall, in more familiar notation the
identity expressed here is: `a ∧ (‌‌‌⋁ᵢ bᵢ) ＝ ⋁ᵢ (a ∧ bᵢ)`.
