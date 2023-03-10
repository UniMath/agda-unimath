# Distributive Lattices

```agda
module order-theory.distributive-lattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.lattices
```

</details>

## Idea

A distributive lattice is a lattice in which meets distribute over joins.

## Definition

```agda
module _
  {l1 l2 : Level} (L : Lattice l1 l2)
  where

  is-distributive-lattice-Prop : Prop l1
  is-distributive-lattice-Prop =
    Π-Prop
      ( element-Lattice L)
      ( λ x →
        Π-Prop
          ( element-Lattice L)
          ( λ y →
            Π-Prop
              ( element-Lattice L)
              ( λ z →
                Id-Prop
                  ( element-lattice-Set L)
                  ( meet-Lattice L x (join-Lattice L y z))
                  ( join-Lattice L (meet-Lattice L x y) (meet-Lattice L x z)))))

  is-distributive-Lattice : UU l1
  is-distributive-Lattice = type-Prop is-distributive-lattice-Prop

  is-prop-is-distributive-Lattice : is-prop is-distributive-Lattice
  is-prop-is-distributive-Lattice =
    is-prop-type-Prop is-distributive-lattice-Prop

Distributive-Lattice :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Distributive-Lattice l1 l2 =
  Σ (Lattice l1 l2) is-distributive-Lattice
```
