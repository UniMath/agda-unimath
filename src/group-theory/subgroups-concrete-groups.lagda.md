# Subgroups of concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.subgroups-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types funext univalence truncations
open import foundation.0-maps funext
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.existential-quantification funext univalence truncations
open import foundation.faithful-maps funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.structure-identity-principle
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import group-theory.concrete-group-actions funext univalence truncations
open import group-theory.concrete-groups funext univalence truncations
open import group-theory.equivalences-concrete-group-actions funext univalence truncations
open import group-theory.homomorphisms-concrete-groups funext univalence truncations
open import group-theory.orbits-concrete-group-actions funext univalence truncations
open import group-theory.transitive-concrete-group-actions funext univalence truncations

open import structured-types.pointed-maps funext univalence truncations
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces funext univalence truncations
open import synthetic-homotopy-theory.loop-spaces funext univalence truncations
```

</details>

## Idea

A subgroup of a concrete group `G` is a pointed transitive `G`-set.

## Definition

```agda
subgroup-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) →
  classifying-type-Concrete-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-Concrete-Group l2 G u =
  Σ ( transitive-action-Concrete-Group l2 G)
    ( λ X → type-Set (action-transitive-action-Concrete-Group G X u))

subgroup-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-Concrete-Group l2 G =
  subgroup-action-Concrete-Group l2 G (shape-Concrete-Group G)

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : subgroup-Concrete-Group l2 G)
  where

  transitive-action-subgroup-Concrete-Group :
    transitive-action-Concrete-Group l2 G
  transitive-action-subgroup-Concrete-Group = pr1 H

  action-subgroup-Concrete-Group : action-Concrete-Group l2 G
  action-subgroup-Concrete-Group =
    action-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  coset-subgroup-Concrete-Group : Set l2
  coset-subgroup-Concrete-Group =
    action-subgroup-Concrete-Group (shape-Concrete-Group G)

  type-coset-subgroup-Concrete-Group : UU l2
  type-coset-subgroup-Concrete-Group = type-Set coset-subgroup-Concrete-Group

  is-transitive-action-subgroup-Concrete-Group :
    is-transitive-action-Concrete-Group G action-subgroup-Concrete-Group
  is-transitive-action-subgroup-Concrete-Group =
    is-transitive-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  mul-transitive-action-subgroup-Concrete-Group :
    type-Concrete-Group G → type-coset-subgroup-Concrete-Group →
    type-coset-subgroup-Concrete-Group
  mul-transitive-action-subgroup-Concrete-Group =
    mul-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  is-abstractly-transitive-transitive-action-subgroup-Concrete-Group :
    is-abstractly-transitive-action-Concrete-Group G
      action-subgroup-Concrete-Group
  is-abstractly-transitive-transitive-action-subgroup-Concrete-Group =
    is-abstractly-transitive-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  classifying-type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  classifying-type-subgroup-Concrete-Group =
    orbit-action-Concrete-Group G action-subgroup-Concrete-Group

  unit-coset-subgroup-Concrete-Group : type-coset-subgroup-Concrete-Group
  unit-coset-subgroup-Concrete-Group = pr2 H

  shape-subgroup-Concrete-Group : classifying-type-subgroup-Concrete-Group
  pr1 shape-subgroup-Concrete-Group = shape-Concrete-Group G
  pr2 shape-subgroup-Concrete-Group = unit-coset-subgroup-Concrete-Group

  classifying-pointed-type-subgroup-Concrete-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-subgroup-Concrete-Group =
    classifying-type-subgroup-Concrete-Group
  pr2 classifying-pointed-type-subgroup-Concrete-Group =
    shape-subgroup-Concrete-Group

  is-connected-classifying-type-subgroup-Concrete-Group :
    is-0-connected classifying-type-subgroup-Concrete-Group
  is-connected-classifying-type-subgroup-Concrete-Group =
    is-transitive-action-subgroup-Concrete-Group

  classifying-inclusion-subgroup-Concrete-Group :
    classifying-type-subgroup-Concrete-Group →
    classifying-type-Concrete-Group G
  classifying-inclusion-subgroup-Concrete-Group = pr1

  preserves-shape-classifying-inclusion-subgroup-Concrete-Group :
    classifying-inclusion-subgroup-Concrete-Group
      shape-subgroup-Concrete-Group ＝
    shape-Concrete-Group G
  preserves-shape-classifying-inclusion-subgroup-Concrete-Group = refl

  classifying-pointed-inclusion-subgroup-Concrete-Group :
    classifying-pointed-type-subgroup-Concrete-Group →∗
    classifying-pointed-type-Concrete-Group G
  pr1 classifying-pointed-inclusion-subgroup-Concrete-Group =
    classifying-inclusion-subgroup-Concrete-Group
  pr2 classifying-pointed-inclusion-subgroup-Concrete-Group =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Group

  is-0-map-classifying-inclusion-subgroup-Concrete-Group :
    is-0-map classifying-inclusion-subgroup-Concrete-Group
  is-0-map-classifying-inclusion-subgroup-Concrete-Group =
    is-0-map-pr1 (λ u → is-set-type-Set (action-subgroup-Concrete-Group u))

  is-faithful-classifying-inclusion-subgroup-Concrete-Group :
    is-faithful classifying-inclusion-subgroup-Concrete-Group
  is-faithful-classifying-inclusion-subgroup-Concrete-Group =
    is-faithful-is-0-map is-0-map-classifying-inclusion-subgroup-Concrete-Group

  type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  type-subgroup-Concrete-Group =
    type-Ω classifying-pointed-type-subgroup-Concrete-Group

  concrete-group-subgroup-Concrete-Group :
    Concrete-Group (l1 ⊔ l2)
  pr1 (pr1 concrete-group-subgroup-Concrete-Group) =
    classifying-pointed-type-subgroup-Concrete-Group
  pr2 (pr1 concrete-group-subgroup-Concrete-Group) =
    is-connected-classifying-type-subgroup-Concrete-Group
  pr2 concrete-group-subgroup-Concrete-Group =
    is-set-is-emb
      ( map-Ω (classifying-pointed-inclusion-subgroup-Concrete-Group))
      ( is-emb-map-Ω
        ( classifying-pointed-inclusion-subgroup-Concrete-Group)
        ( is-faithful-classifying-inclusion-subgroup-Concrete-Group))
      ( is-set-type-Concrete-Group G)

  hom-inclusion-subgroup-Concrete-Group :
    hom-Concrete-Group concrete-group-subgroup-Concrete-Group G
  pr1 hom-inclusion-subgroup-Concrete-Group =
    classifying-inclusion-subgroup-Concrete-Group
  pr2 hom-inclusion-subgroup-Concrete-Group =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Group
```

## Properties

### The type of subgroups of a group is a set

```agda
subtype-preserves-unit-coset-equiv-action-Concrete-Group :
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (X : subgroup-Concrete-Group l2 G)
  (Y : subgroup-Concrete-Group l3 G) →
  subtype l3
    ( equiv-action-Concrete-Group G
      ( action-subgroup-Concrete-Group G X)
      ( action-subgroup-Concrete-Group G Y))
subtype-preserves-unit-coset-equiv-action-Concrete-Group G X Y e =
  Id-Prop
    ( coset-subgroup-Concrete-Group G Y)
    ( map-equiv-action-Concrete-Group G
      ( action-subgroup-Concrete-Group G X)
      ( action-subgroup-Concrete-Group G Y)
      ( e)
      ( unit-coset-subgroup-Concrete-Group G X))
    ( unit-coset-subgroup-Concrete-Group G Y)

equiv-subgroup-Concrete-Group :
  {l1 l2 l3 : Level} (G : Concrete-Group l1) → subgroup-Concrete-Group l2 G →
  subgroup-Concrete-Group l3 G → UU (l1 ⊔ l2 ⊔ l3)
equiv-subgroup-Concrete-Group G X Y =
  type-subtype
    ( subtype-preserves-unit-coset-equiv-action-Concrete-Group G X Y)

extensionality-subgroup-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X Y : subgroup-Concrete-Group l2 G) →
  (X ＝ Y) ≃ equiv-subgroup-Concrete-Group G X Y
extensionality-subgroup-Concrete-Group G X =
  extensionality-Σ
    ( λ {Y} y e →
      ( map-equiv
        ( e (shape-Concrete-Group G))
        ( unit-coset-subgroup-Concrete-Group G X)) ＝
      ( y))
    ( id-equiv-action-Concrete-Group G (action-subgroup-Concrete-Group G X))
    ( refl)
    ( extensionality-transitive-action-Concrete-Group G
      ( transitive-action-subgroup-Concrete-Group G X))
    ( λ x → id-equiv)

is-set-subgroup-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) →
  is-set (subgroup-Concrete-Group l2 G)
is-set-subgroup-Concrete-Group G X Y =
  is-prop-equiv
    ( extensionality-subgroup-Concrete-Group G X Y)
    ( λ e f →
      is-proof-irrelevant-is-prop
        ( is-set-type-subtype
          ( subtype-preserves-unit-coset-equiv-action-Concrete-Group G X Y)
          ( is-set-equiv-action-Concrete-Group G
            ( action-subgroup-Concrete-Group G X)
            ( action-subgroup-Concrete-Group G Y))
          ( e)
          ( f))
        ( eq-type-subtype
          ( subtype-preserves-unit-coset-equiv-action-Concrete-Group G X Y)
          ( eq-htpy-equiv-action-Concrete-Group G
            ( action-subgroup-Concrete-Group G X)
            ( action-subgroup-Concrete-Group G Y)
            ( pr1 e)
            ( pr1 f)
            ( htpy-exists-equiv-transitive-action-Concrete-Group G
              ( transitive-action-subgroup-Concrete-Group G X)
              ( transitive-action-subgroup-Concrete-Group G Y)
              ( pr1 e)
              ( pr1 f)
              ( intro-exists
                ( unit-coset-subgroup-Concrete-Group G X)
                ( pr2 e ∙ inv (pr2 f)))))))
```
