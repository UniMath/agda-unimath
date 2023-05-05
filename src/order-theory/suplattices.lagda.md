# Suplattices

```agda
module order-theory.suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
```

</details>

## Idea

An **`l`-suplattice** is a poset which has all joins of families of elements
indexed by a type of universe level `l`.

## Definitions

### Order theoretic sup lattices

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-suplattice-Poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-suplattice-Poset-Prop =
    Π-Prop
      (UU l3)
      (λ I →
        Π-Prop
          ( I → element-Poset P)
          ( λ f → has-least-upper-bound-family-of-elements-Poset-Prop P f))

  is-suplattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-suplattice-Poset = type-Prop is-suplattice-Poset-Prop

  is-prop-suplattice-Poset : is-prop is-suplattice-Poset
  is-prop-suplattice-Poset = is-prop-type-Prop is-suplattice-Poset-Prop

Suplattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Suplattice l1 l2 l3 = Σ (Poset l1 l2) (λ P → is-suplattice-Poset l3 P)
```

We now develop the tools that allow us to work with the components of a sup
lattice.

```agda
module _
  {l1 l2 l3 : Level} (A : Suplattice l1 l2 l3)
  where

  poset-Suplattice : Poset l1 l2
  poset-Suplattice = pr1 A

  element-Suplattice : UU l1
  element-Suplattice = element-Poset poset-Suplattice

  leq-Suplattice-Prop : (x y : element-Suplattice) → Prop l2
  leq-Suplattice-Prop = leq-Poset-Prop poset-Suplattice

  leq-Suplattice : (x y : element-Suplattice) → UU l2
  leq-Suplattice = leq-Poset poset-Suplattice

  is-prop-leq-Suplattice :
    (x y : element-Suplattice) → is-prop (leq-Suplattice x y)
  is-prop-leq-Suplattice = is-prop-leq-Poset poset-Suplattice

  refl-leq-Suplattice :
    (x : element-Suplattice) → leq-Suplattice x x
  refl-leq-Suplattice = refl-leq-Poset poset-Suplattice

  antisymmetric-leq-Suplattice :
    (x y : element-Suplattice) →
    leq-Suplattice x y → leq-Suplattice y x → x ＝ y
  antisymmetric-leq-Suplattice =
    antisymmetric-leq-Poset poset-Suplattice

  transitive-leq-Suplattice :
    (x y z : element-Suplattice) →
    leq-Suplattice y z → leq-Suplattice x y →
    leq-Suplattice x z
  transitive-leq-Suplattice = transitive-leq-Poset poset-Suplattice

  is-set-element-Suplattice : is-set element-Suplattice
  is-set-element-Suplattice = is-set-element-Poset poset-Suplattice

  set-Suplattice : Set l1
  set-Suplattice = set-Poset poset-Suplattice

  is-suplattice-Suplattice :
    is-suplattice-Poset l3 poset-Suplattice
  is-suplattice-Suplattice = pr2 A

  sup-Suplattice :
    (I : UU l3) → (I → element-Suplattice) → element-Suplattice
  sup-Suplattice I f = pr1 (is-suplattice-Suplattice I f)

  is-least-upper-bound-family-of-elements-sup-Suplattice :
    (I : UU l3) → (f : I → element-Suplattice) →
    is-least-upper-bound-family-of-elements-Poset poset-Suplattice f
      (sup-Suplattice I f)
  is-least-upper-bound-family-of-elements-sup-Suplattice I f =
    pr2 (is-suplattice-Suplattice I f)
```
