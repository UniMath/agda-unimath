# Stabilizers of concrete group actions

```agda
module group-theory.stabilizer-groups-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.orbits-concrete-group-actions
open import group-theory.subgroups-concrete-groups
open import group-theory.transitive-concrete-group-actions
```

</details>

## Idea

The stabilizer of an element `x : X pt` of a concrete G-set `X : BG → Set` is the connected component of `pair pt x` in the type of orbits of `X`. Its loop space is indeed the type of elements `g : G` such that `g x = x`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  action-stabilizer-action-Concrete-Group :
    type-action-Concrete-Group G X → action-Concrete-Group (l1 ⊔ l2) G
  action-stabilizer-action-Concrete-Group x u =
    set-subset
      ( X u)
      ( λ y → mere-eq-Prop (pair (shape-Concrete-Group G) x) (pair u y))

  is-transitive-action-stabilizer-action-Concrete-Group :
    (x : type-action-Concrete-Group G X) →
    is-transitive-action-Concrete-Group G
      ( action-stabilizer-action-Concrete-Group x)
  is-transitive-action-stabilizer-action-Concrete-Group x =
    is-0-connected-equiv'
      ( assoc-Σ
        ( classifying-type-Concrete-Group G)
        ( type-Set ∘ X)
        ( λ uy →
          mere-eq (pair (shape-Concrete-Group G) x) (pair (pr1 uy) (pr2 uy))))
      ( is-0-connected-mere-eq
        ( pair (pair (shape-Concrete-Group G) x) refl-mere-eq)
        ( λ (pair uy p) →
          apply-universal-property-trunc-Prop p
            ( mere-eq-Prop
              ( pair (pair (shape-Concrete-Group G) x) refl-mere-eq)
              ( pair uy p))
            ( λ q →
              unit-trunc-Prop
                ( eq-type-subtype
                  ( mere-eq-Prop (pair (shape-Concrete-Group G) x))
                  ( q)))))

  subgroup-stabilizer-action-Concrete-Group :
    (x : type-action-Concrete-Group G X) → subgroup-Concrete-Group (l1 ⊔ l2) G
  pr1 (pr1 (subgroup-stabilizer-action-Concrete-Group x)) =
    action-stabilizer-action-Concrete-Group x
  pr2 (pr1 (subgroup-stabilizer-action-Concrete-Group x)) =
    is-transitive-action-stabilizer-action-Concrete-Group x
  pr1 (pr2 (subgroup-stabilizer-action-Concrete-Group x)) = x
  pr2 (pr2 (subgroup-stabilizer-action-Concrete-Group x)) = refl-mere-eq
```
