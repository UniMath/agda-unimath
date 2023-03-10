# Sup Lattices

```agda
module order-theory.sup-lattices where
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
open import order-theory.posets
```

</details>

## Idea
A sup lattice is a poset in which every family of elements has a least upperbound.
For full generality we will consider 3 different universe levels: one for the underlying type, one for
the order relation and one for the indexing type.

## Definitions

### Order theoretic sup lattices

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-sup-lattice-poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-sup-lattice-poset-Prop =
    Π-Prop
      (UU l3)
      (λ I →
        Π-Prop
          ( I → element-Poset P )
          ( λ f → has-least-upper-bound-family-poset-Prop P f))

  is-sup-lattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-sup-lattice-Poset = type-Prop is-sup-lattice-poset-Prop

  is-prop-sup-lattice-Poset : is-prop is-sup-lattice-Poset
  is-prop-sup-lattice-Poset = is-prop-type-Prop is-sup-lattice-poset-Prop

Sup-Lattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Sup-Lattice l1 l2 l3 = Σ (Poset l1 l2) (λ P → is-sup-lattice-Poset l3 P)

```

We now develop the tools that allow us to work with the components of a sup lattice.

```agda

module _
  {l1 l2 l3 : Level} (A : Sup-Lattice l1 l2 l3)
  where

  poset-Sup-Lattice : Poset l1 l2
  poset-Sup-Lattice = pr1 A

  element-Sup-Lattice : UU l1    {- could we use carrier instead of element? -}
  element-Sup-Lattice = element-Poset poset-Sup-Lattice

  leq-sup-lattice-Prop : (x y : element-Sup-Lattice) → Prop l2
  leq-sup-lattice-Prop = leq-poset-Prop poset-Sup-Lattice

  leq-Sup-Lattice : (x y : element-Sup-Lattice) → UU l2
  leq-Sup-Lattice = leq-Poset poset-Sup-Lattice

  is-prop-leq-Sup-Lattice :
    (x y : element-Sup-Lattice) → is-prop (leq-Sup-Lattice x y)
  is-prop-leq-Sup-Lattice = is-prop-leq-Poset poset-Sup-Lattice

  refl-leq-Sup-Lattice :
    (x : element-Sup-Lattice) → leq-Sup-Lattice x x
  refl-leq-Sup-Lattice = refl-leq-Poset poset-Sup-Lattice

  antisymmetric-leq-Sup-Lattice :
    (x y : element-Sup-Lattice) →
    leq-Sup-Lattice x y → leq-Sup-Lattice y x → x ＝ y
  antisymmetric-leq-Sup-Lattice =
    antisymmetric-leq-Poset poset-Sup-Lattice

  transitive-leq-Sup-Lattice :
    (x y z : element-Sup-Lattice) →
    leq-Sup-Lattice y z → leq-Sup-Lattice x y →
    leq-Sup-Lattice x z
  transitive-leq-Sup-Lattice = transitive-leq-Poset poset-Sup-Lattice

  is-set-element-Sup-Lattice : is-set element-Sup-Lattice
  is-set-element-Sup-Lattice = is-set-element-Poset poset-Sup-Lattice

  element-sup-lattice-Set : Set l1
  element-sup-lattice-Set = element-poset-Set poset-Sup-Lattice

  is-sup-lattice-Sup-Lattice :
    is-sup-lattice-Poset l3 poset-Sup-Lattice
  is-sup-lattice-Sup-Lattice = pr2 A

  sup-lattice-Sup-Lattice : Sup-Lattice l1 l2 l3
  pr1 sup-lattice-Sup-Lattice = poset-Sup-Lattice
  pr2 sup-lattice-Sup-Lattice = is-sup-lattice-Sup-Lattice

  sup-Sup-Lattice :
    (I : UU l3) → (I → element-Sup-Lattice) → element-Sup-Lattice
  sup-Sup-Lattice I f = pr1 (is-sup-lattice-Sup-Lattice I f)

  is-least-upper-bound-family-sup-Sup-Lattice :
    (I : UU l3) → (f : I → element-Sup-Lattice) →
    is-least-upper-bound-family-Poset poset-Sup-Lattice f
      (sup-Sup-Lattice I f)
  is-least-upper-bound-family-sup-Sup-Lattice I f = pr2 (is-sup-lattice-Sup-Lattice I f)

```
