# Quotient groups of concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.quotient-groups-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext univalence truncations
open import foundation.0-images-of-maps funext univalence truncations
open import foundation.1-types funext univalence
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.mere-equality funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.sets funext univalence
open import foundation.subtype-identity-principle
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import group-theory.concrete-groups funext univalence truncations
open import group-theory.equivalences-concrete-group-actions funext univalence truncations
open import group-theory.mere-equivalences-concrete-group-actions funext univalence truncations
open import group-theory.normal-subgroups-concrete-groups funext univalence truncations
open import group-theory.transitive-concrete-group-actions funext univalence truncations

open import higher-group-theory.higher-groups funext univalence truncations

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces funext univalence truncations
```

</details>

## Idea

Given a normal subgroup `N` of a concrete group `G`, the quotient group `G/N` is
a concrete group that satisfies the universal property that for any concrete
group homomorphism `f : G → H` such that the kernel of `f` is contained in `N`,
then `f` extends uniquely to a group homomorphism `G/N → H`.

The quotient `G/N` can be constructed in several ways.

1. We can construct `G/N` as the type of `G`-sets merely equivalent to the coset
   action of `N`. Since this construction is reminiscent of the torsor
   construction of BG, we call this the **standard construction** of `G/N`.
2. We can construct `G/N` as the 0-image of the coset action `N : BG → U`. We
   call this the **0-image construction** of `G/N`.

## Definitions

### The standard construction of `G/N`

```agda
module _
  { l1 l2 : Level} (G : Concrete-Group l1)
  ( N : normal-subgroup-Concrete-Group l2 G)
  where

  classifying-type-quotient-Concrete-Group : UU (l1 ⊔ lsuc l2)
  classifying-type-quotient-Concrete-Group =
    Σ ( transitive-action-Concrete-Group l2 G)
      ( λ X →
        mere-equiv-action-Concrete-Group G
        ( action-normal-subgroup-Concrete-Group G N)
        ( action-transitive-action-Concrete-Group G X))

  shape-quotient-Concrete-Group :
    classifying-type-quotient-Concrete-Group
  pr1 shape-quotient-Concrete-Group =
    transitive-action-normal-subgroup-Concrete-Group G N
  pr2 shape-quotient-Concrete-Group =
    refl-mere-equiv-action-Concrete-Group G
      ( action-normal-subgroup-Concrete-Group G N)

  classifying-pointed-type-quotient-Concrete-Group :
    Pointed-Type (l1 ⊔ lsuc l2)
  pr1 classifying-pointed-type-quotient-Concrete-Group =
    classifying-type-quotient-Concrete-Group
  pr2 classifying-pointed-type-quotient-Concrete-Group =
    shape-quotient-Concrete-Group

  type-quotient-Concrete-Group : UU (l1 ⊔ lsuc l2)
  type-quotient-Concrete-Group =
    type-Ω classifying-pointed-type-quotient-Concrete-Group

  extensionality-classifying-type-quotient-Concrete-Group :
    (u v : classifying-type-quotient-Concrete-Group) →
    (u ＝ v) ≃ equiv-transitive-action-Concrete-Group G (pr1 u) (pr1 v)
  extensionality-classifying-type-quotient-Concrete-Group u =
    extensionality-type-subtype
      ( λ (X : transitive-action-Concrete-Group l2 G) →
        mere-equiv-prop-action-Concrete-Group G
          ( action-normal-subgroup-Concrete-Group G N)
          ( action-transitive-action-Concrete-Group G X))
      ( pr2 u)
      ( id-equiv-transitive-action-Concrete-Group G
        ( pr1 u))
      ( extensionality-transitive-action-Concrete-Group G (pr1 u))

  is-0-connected-classifying-type-quotient-Concrete-Group :
    is-0-connected classifying-type-quotient-Concrete-Group
  is-0-connected-classifying-type-quotient-Concrete-Group =
    is-0-connected-mere-eq
      ( shape-quotient-Concrete-Group)
      ( λ (pair u p) →
        apply-universal-property-trunc-Prop p
          ( mere-eq-Prop
            ( shape-quotient-Concrete-Group)
            ( pair u p))
          ( λ e →
            unit-trunc-Prop
              ( eq-type-subtype
                ( λ X →
                  mere-equiv-prop-action-Concrete-Group G
                    ( action-normal-subgroup-Concrete-Group G N)
                    ( action-transitive-action-Concrete-Group G X))
                ( eq-type-subtype
                  ( is-transitive-prop-action-Concrete-Group G)
                  ( eq-equiv-action-Concrete-Group G
                    ( action-normal-subgroup-Concrete-Group G N)
                    ( pr1 u)
                    ( e))))))

  is-1-type-classifying-type-quotient-Concrete-Group :
    is-1-type classifying-type-quotient-Concrete-Group
  is-1-type-classifying-type-quotient-Concrete-Group =
    is-1-type-type-subtype
      ( λ X →
        mere-equiv-prop-action-Concrete-Group G
          ( action-normal-subgroup-Concrete-Group G N)
          ( action-transitive-action-Concrete-Group G X))
      ( is-1-type-transitive-action-Concrete-Group G)

  is-set-type-quotient-Concrete-Group :
    is-set type-quotient-Concrete-Group
  is-set-type-quotient-Concrete-Group =
    is-1-type-classifying-type-quotient-Concrete-Group
      shape-quotient-Concrete-Group
      shape-quotient-Concrete-Group

  ∞-group-quotient-Concrete-Group : ∞-Group (l1 ⊔ lsuc l2)
  pr1 ∞-group-quotient-Concrete-Group =
    classifying-pointed-type-quotient-Concrete-Group
  pr2 ∞-group-quotient-Concrete-Group =
    is-0-connected-classifying-type-quotient-Concrete-Group

  concrete-group-quotient-Concrete-Group :
    Concrete-Group (l1 ⊔ lsuc l2)
  pr1 concrete-group-quotient-Concrete-Group =
    ∞-group-quotient-Concrete-Group
  pr2 concrete-group-quotient-Concrete-Group =
    is-set-type-quotient-Concrete-Group
```

### The 0-image construction of `G/N`

```agda
module _
  { l1 l2 : Level} (G : Concrete-Group l1)
  ( N : normal-subgroup-Concrete-Group l2 G)
  where

  classifying-type-0-image-quotient-Concrete-Group : UU (l1 ⊔ lsuc l2)
  classifying-type-0-image-quotient-Concrete-Group =
    0-im (action-normal-subgroup-Concrete-Group G N)

  shape-0-image-quotient-Concrete-Group :
    classifying-type-0-image-quotient-Concrete-Group
  shape-0-image-quotient-Concrete-Group =
    unit-0-im
      ( action-normal-subgroup-Concrete-Group G N)
      ( shape-Concrete-Group G)

  classifying-pointed-type-0-image-quotient-Concrete-Group :
    Pointed-Type (l1 ⊔ lsuc l2)
  pr1 classifying-pointed-type-0-image-quotient-Concrete-Group =
    classifying-type-0-image-quotient-Concrete-Group
  pr2 classifying-pointed-type-0-image-quotient-Concrete-Group =
    shape-0-image-quotient-Concrete-Group

  type-0-image-quotient-Concrete-Group : UU (l1 ⊔ lsuc l2)
  type-0-image-quotient-Concrete-Group =
    type-Ω classifying-pointed-type-0-image-quotient-Concrete-Group
```
