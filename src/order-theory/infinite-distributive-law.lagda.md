# Infinite distributive law

```agda
module order-theory.infinite-distributive-law where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.sup-lattices
```

</details>

## Idea
Let A be a poset that has all binary meets and arbitrary joins (which we call sups).
We can show that all sup lattices have binary meets (and we plan to in another file),
but this economy offers little benefit here.
The infinite distributive law states:
for all a : A and for all families b : I → A the following identity holds
                  a ∧ (‌‌‌⋁ᵢ bᵢ) ＝ ⋁ᵢ (a ∧ bᵢ)
Note: One could inquire about the dual infinite distributive law but it is not needed at this time.

```agda

module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-meet-sup-lattice-poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-meet-sup-lattice-poset-Prop =
    prod-Prop (is-meet-semilattice-poset-Prop P) (is-sup-lattice-poset-Prop l3 P)

  is-meet-sup-lattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-meet-sup-lattice-Poset = type-Prop is-meet-sup-lattice-poset-Prop

  is-prop-is-meet-sup-lattice-Poset : is-prop is-meet-sup-lattice-Poset
  is-prop-is-meet-sup-lattice-Poset = is-prop-type-Prop is-meet-sup-lattice-poset-Prop

Meet-Sup-Lattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Meet-Sup-Lattice l1 l2 l3 =
  Σ (Poset l1 l2) (is-meet-sup-lattice-Poset l3)

```

## We need to provide the appropriate components to state the infinite distributive law.

```agda

module _
  {l1 l2 l3 : Level} (A : Meet-Sup-Lattice l1 l2 l3)
  where

  poset-Meet-Sup-Lattice : Poset l1 l2
  poset-Meet-Sup-Lattice = pr1 A

  element-Meet-Sup-Lattice : UU l1
  element-Meet-Sup-Lattice =
    element-Poset poset-Meet-Sup-Lattice

  leq-meet-sup-lattice-Prop : (x y : element-Meet-Sup-Lattice) → Prop l2
  leq-meet-sup-lattice-Prop = leq-poset-Prop poset-Meet-Sup-Lattice

  leq-Meet-Sup-Lattice : (x y : element-Meet-Sup-Lattice) → UU l2
  leq-Meet-Sup-Lattice = leq-Poset poset-Meet-Sup-Lattice

  is-prop-leq-Meet-Sup-Lattice :
    (x y : element-Meet-Sup-Lattice) → is-prop (leq-Meet-Sup-Lattice x y)
  is-prop-leq-Meet-Sup-Lattice = is-prop-leq-Poset poset-Meet-Sup-Lattice

  refl-leq-Meet-Sup-Lattice :
    (x : element-Meet-Sup-Lattice) → leq-Meet-Sup-Lattice x x
  refl-leq-Meet-Sup-Lattice = refl-leq-Poset poset-Meet-Sup-Lattice

  antisymmetric-leq-Meet-Sup-Lattice :
    (x y : element-Meet-Sup-Lattice) →
    leq-Meet-Sup-Lattice x y → leq-Meet-Sup-Lattice y x → x ＝ y
  antisymmetric-leq-Meet-Sup-Lattice =
    antisymmetric-leq-Poset poset-Meet-Sup-Lattice

  transitive-leq-Meet-Sup-Lattice :
    (x y z : element-Meet-Sup-Lattice) →
    leq-Meet-Sup-Lattice y z → leq-Meet-Sup-Lattice x y →
    leq-Meet-Sup-Lattice x z
  transitive-leq-Meet-Sup-Lattice = transitive-leq-Poset poset-Meet-Sup-Lattice

  is-set-element-Meet-Sup-Lattice : is-set element-Meet-Sup-Lattice
  is-set-element-Meet-Sup-Lattice = is-set-element-Poset poset-Meet-Sup-Lattice

  element-meet-sup-lattice-Set : Set l1
  element-meet-sup-lattice-Set = element-poset-Set poset-Meet-Sup-Lattice

  is-meet-semilattice-Meet-Sup-Lattice :
    is-meet-semilattice-Poset poset-Meet-Sup-Lattice
  is-meet-semilattice-Meet-Sup-Lattice = pr1 (pr2 A)

  meet-semilattice-Meet-Sup-Lattice : Meet-Semilattice l1 l2
  meet-semilattice-Meet-Sup-Lattice = ( poset-Meet-Sup-Lattice , is-meet-semilattice-Meet-Sup-Lattice )

  is-sup-lattice-Meet-Sup-Lattice :
    is-sup-lattice-Poset l3 poset-Meet-Sup-Lattice
  is-sup-lattice-Meet-Sup-Lattice = pr2 (pr2 A)

  sup-lattice-Meet-Sup-Lattice : Sup-Lattice l1 l2 l3
  sup-lattice-Meet-Sup-Lattice = ( poset-Meet-Sup-Lattice , is-sup-lattice-Meet-Sup-Lattice )

  meet-sup-lattice-Meet-Sup-Lattice :
    Meet-Sup-Lattice l1 l2 l3
  pr1 meet-sup-lattice-Meet-Sup-Lattice =
    poset-Meet-Sup-Lattice
  pr1 (pr2 meet-sup-lattice-Meet-Sup-Lattice) =
    is-meet-semilattice-Meet-Sup-Lattice
  pr2 (pr2 meet-sup-lattice-Meet-Sup-Lattice) =
    is-sup-lattice-Meet-Sup-Lattice

  meet-Meet-Sup-Lattice :
    (x y : element-Meet-Sup-Lattice) →
    element-Meet-Sup-Lattice
  meet-Meet-Sup-Lattice x y = pr1 (is-meet-semilattice-Meet-Sup-Lattice x y)

  sup-Meet-Sup-Lattice :
    (I : UU l3) → (I → element-Meet-Sup-Lattice) →
    element-Meet-Sup-Lattice
  sup-Meet-Sup-Lattice I f = pr1 (is-sup-lattice-Meet-Sup-Lattice I f)

```

## Characterize the identity type.

## We now state the infinite distributive law

```agda

distributive-law-meet-sup-lattice : (l1 l2 l3 : Level) → (Meet-Sup-Lattice l1 l2 l3) → UU (l1 ⊔ lsuc l3)
distributive-law-meet-sup-lattice l1 l2 l3 A =
  (a : element-Meet-Sup-Lattice A) → {I : UU l3} →
  (b : I → element-Meet-Sup-Lattice A) →
  (meet-Meet-Sup-Lattice A a (sup-Meet-Sup-Lattice A I b) ＝
  sup-Meet-Sup-Lattice A I (λ i → (meet-Meet-Sup-Lattice A a (b i))))

```

This notation is not easy on the eye, but recall, in more familiar notation the identity expressed here is:
                                a ∧ (‌‌‌⋁ᵢ bᵢ) ＝ ⋁ᵢ (a ∧ bᵢ)

Show that the identity is a prop.
