# Stabilizers of concrete group actions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.stabilizer-groups-concrete-group-actions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.mere-equality funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.concrete-group-actions funext univalence truncations
open import group-theory.concrete-groups funext univalence truncations
open import group-theory.subgroups-concrete-groups funext univalence truncations
open import group-theory.transitive-concrete-group-actions funext univalence truncations
```

</details>

## Idea

The **stabilizer** of an element `x : X point` of a
[concrete `G`-set](group-theory.concrete-group-actions.md) `X : BG → Set` is the
[connected component](foundation.connected-components.md) at the element
`(point , x)` in the type of
[orbits](group-theory.orbits-concrete-group-actions.md) of `X`. This type is a
indeed [concrete group](group-theory.concrete-groups.md) of which the underlying
type is the type of elements `g : G` such that `g x = x`.

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
      ( λ y → mere-eq-Prop (shape-Concrete-Group G , x) (u , y))

  is-transitive-action-stabilizer-action-Concrete-Group :
    (x : type-action-Concrete-Group G X) →
    is-transitive-action-Concrete-Group G
      ( action-stabilizer-action-Concrete-Group x)
  is-transitive-action-stabilizer-action-Concrete-Group x =
    is-0-connected-equiv'
      ( associative-Σ
        ( classifying-type-Concrete-Group G)
        ( type-Set ∘ X)
        ( mere-eq (shape-Concrete-Group G , x)))
      ( is-0-connected-mere-eq
        ( ( shape-Concrete-Group G , x) ,
          ( refl-mere-eq (shape-Concrete-Group G , x)))
        ( λ (uy , p) →
          apply-universal-property-trunc-Prop p
            ( mere-eq-Prop
              ( ( shape-Concrete-Group G , x) ,
                ( refl-mere-eq (shape-Concrete-Group G , x)))
              ( uy , p))
            ( λ q →
              unit-trunc-Prop
                ( eq-type-subtype
                  ( mere-eq-Prop (shape-Concrete-Group G , x))
                  ( q)))))

  subgroup-stabilizer-action-Concrete-Group :
    (x : type-action-Concrete-Group G X) → subgroup-Concrete-Group (l1 ⊔ l2) G
  pr1 (pr1 (subgroup-stabilizer-action-Concrete-Group x)) =
    action-stabilizer-action-Concrete-Group x
  pr2 (pr1 (subgroup-stabilizer-action-Concrete-Group x)) =
    is-transitive-action-stabilizer-action-Concrete-Group x
  pr1 (pr2 (subgroup-stabilizer-action-Concrete-Group x)) = x
  pr2 (pr2 (subgroup-stabilizer-action-Concrete-Group x)) =
    refl-mere-eq (shape-Concrete-Group G , x)
```

## External links

- [stabilizer group](https://ncatlab.org/nlab/show/stabilizer+group) at $n$Lab
- [Fixed points and stabilizer subgroups](https://en.wikipedia.org/wiki/Group_action#Fixed_points_and_stabilizer_subgroups)
  at Wikipedia
- [Isotropy Group](https://mathworld.wolfram.com/IsotropyGroup.html) at Wolfram
  MathWorld
- [Isotropy group](https://encyclopediaofmath.org/wiki/Isotropy_group) at
  Encyclopedia of Mathematics
