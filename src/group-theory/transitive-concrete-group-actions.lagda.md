# Transitive concrete group actions

```agda
module group-theory.transitive-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-group-actions

open import higher-group-theory.transitive-higher-group-actions
```

</details>

## Idea

Consider a [concrete group](group-theory.concrete-groups.md) `G` and a
[concrete group action](group-theory.concrete-group-actions.md) of `G` on `X`.
We say that `X` is **transitive** if its type of
[orbits](group-theory.orbits-concrete-group-actions.md) is
[connected](foundation.connected-types.md).

[Equivalently](foundation.logical-equivalences.md), we say that `X` is
**abstractly transitive** if the underlying type of `X` is
[inhabited](foundation.inhabited-types.md) and for any element `x : X (sh G)` of
the underlying type of `X` the action map

```text
  g ↦ mul-action-Concrete-Group G X g x
```

is [surjective](foundation.surjective-maps.md).

Note that it is necessary to include the condition that `X` is inhabited in the
condition that `G` acts transitively on `X`. A first reason is that this makes
the condition of being abstractly transitive equivalent to the condition of
being transitive. A second reason is that this way we will be able to recover
the familiar property that a `G`-action `X` is a `G`-torsor if and only if it is
both [free](group-theory.free-concrete-group-actions.md) and transitive.

## Definition

### The predicate of being a transitive concrete group action

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-transitive-prop-action-Concrete-Group : Prop (l1 ⊔ l2)
  is-transitive-prop-action-Concrete-Group =
    is-transitive-prop-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-transitive-action-Concrete-Group : UU (l1 ⊔ l2)
  is-transitive-action-Concrete-Group =
    is-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-prop-is-transitive-action-Concrete-Group :
    is-prop is-transitive-action-Concrete-Group
  is-prop-is-transitive-action-Concrete-Group =
    is-prop-is-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)
```

### The predicate of being an abstractly transitive concrete group action

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-abstractly-transitive-prop-action-Concrete-Group : Prop (l1 ⊔ l2)
  is-abstractly-transitive-prop-action-Concrete-Group =
    is-abstractly-transitive-prop-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-abstractly-transitive-action-Concrete-Group : UU (l1 ⊔ l2)
  is-abstractly-transitive-action-Concrete-Group =
    is-abstractly-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-prop-is-abstractly-transitive-action-Concrete-Group :
    is-prop is-abstractly-transitive-action-Concrete-Group
  is-prop-is-abstractly-transitive-action-Concrete-Group =
    is-prop-is-abstractly-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)
```

### Transitive concrete group actions

```agda
transitive-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
transitive-action-Concrete-Group l2 G =
  type-subtype (is-transitive-prop-action-Concrete-Group {l2 = l2} G)

module _
  {l1 l2 : Level} (G : Concrete-Group l1)
  (X : transitive-action-Concrete-Group l2 G)
  where

  action-transitive-action-Concrete-Group :
    action-Concrete-Group l2 G
  action-transitive-action-Concrete-Group = pr1 X

  is-transitive-transitive-action-Concrete-Group :
    is-transitive-action-Concrete-Group G
      action-transitive-action-Concrete-Group
  is-transitive-transitive-action-Concrete-Group = pr2 X

  transitive-action-∞-group-transitive-action-Concrete-Group :
    transitive-action-∞-Group l2 (∞-group-Concrete-Group G)
  pr1 transitive-action-∞-group-transitive-action-Concrete-Group =
    type-Set ∘ action-transitive-action-Concrete-Group
  pr2 transitive-action-∞-group-transitive-action-Concrete-Group =
    is-transitive-transitive-action-Concrete-Group

  set-transitive-action-Concrete-Group : Set l2
  set-transitive-action-Concrete-Group =
    set-action-Concrete-Group G action-transitive-action-Concrete-Group

  type-transitive-action-Concrete-Group : UU l2
  type-transitive-action-Concrete-Group =
    type-action-Concrete-Group G action-transitive-action-Concrete-Group

  is-set-type-transitive-action-Concrete-Group :
    is-set type-transitive-action-Concrete-Group
  is-set-type-transitive-action-Concrete-Group =
    is-set-type-action-Concrete-Group G action-transitive-action-Concrete-Group

  is-inhabited-type-transitive-action-Concrete-Group :
    is-inhabited type-transitive-action-Concrete-Group
  is-inhabited-type-transitive-action-Concrete-Group =
    is-inhabited-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( transitive-action-∞-group-transitive-action-Concrete-Group)

  inhabited-type-transitive-action-Concrete-Group :
    Inhabited-Type l2
  inhabited-type-transitive-action-Concrete-Group =
    inhabited-type-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( transitive-action-∞-group-transitive-action-Concrete-Group)

  mul-transitive-action-Concrete-Group :
    type-Concrete-Group G → type-transitive-action-Concrete-Group →
    type-transitive-action-Concrete-Group
  mul-transitive-action-Concrete-Group =
    mul-action-Concrete-Group G action-transitive-action-Concrete-Group

  is-abstractly-transitive-transitive-action-Concrete-Group :
    is-abstractly-transitive-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group)
  is-abstractly-transitive-transitive-action-Concrete-Group =
    is-abstractly-transitive-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( transitive-action-∞-group-transitive-action-Concrete-Group)

  is-surjective-mul-right-transitive-action-Concrete-Group :
    (x : type-transitive-action-Concrete-Group) →
    is-surjective (λ g → mul-transitive-action-Concrete-Group g x)
  is-surjective-mul-right-transitive-action-Concrete-Group =
    is-surjective-mul-right-transitive-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( transitive-action-∞-group-transitive-action-Concrete-Group)
```

## Properties

### Characterization of the identity type of transitive actions of a concrete group

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1)
  (X : transitive-action-Concrete-Group l2 G)
  where

  equiv-transitive-action-Concrete-Group :
    {l3 : Level} (Y : transitive-action-Concrete-Group l3 G) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-transitive-action-Concrete-Group Y =
    equiv-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group G X)
      ( action-transitive-action-Concrete-Group G Y)

  map-equiv-transitive-action-Concrete-Group :
    {l3 : Level} (Y : transitive-action-Concrete-Group l3 G) →
    equiv-transitive-action-Concrete-Group Y →
    type-transitive-action-Concrete-Group G X →
    type-transitive-action-Concrete-Group G Y
  map-equiv-transitive-action-Concrete-Group Y =
    map-equiv-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group G X)
      ( action-transitive-action-Concrete-Group G Y)

  preserves-mul-equiv-transitive-action-Concrete-Group :
    {l3 : Level} (Y : transitive-action-Concrete-Group l3 G) →
    (e : equiv-transitive-action-Concrete-Group Y) (g : type-Concrete-Group G)
    (x : type-transitive-action-Concrete-Group G X) →
    ( map-equiv-transitive-action-Concrete-Group Y e
      ( mul-transitive-action-Concrete-Group G X g x)) ＝
    ( mul-transitive-action-Concrete-Group G Y g
      ( map-equiv-transitive-action-Concrete-Group Y e x))
  preserves-mul-equiv-transitive-action-Concrete-Group Y =
    preserves-mul-equiv-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group G X)
      ( action-transitive-action-Concrete-Group G Y)

  id-equiv-transitive-action-Concrete-Group :
    equiv-transitive-action-Concrete-Group X
  id-equiv-transitive-action-Concrete-Group =
    id-equiv-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group G X)

  extensionality-transitive-action-Concrete-Group :
    (Y : transitive-action-Concrete-Group l2 G) →
    (X ＝ Y) ≃ equiv-transitive-action-Concrete-Group Y
  extensionality-transitive-action-Concrete-Group Y =
    ( extensionality-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group G X)
      ( action-transitive-action-Concrete-Group G Y)) ∘e
    ( extensionality-type-subtype'
      ( is-transitive-prop-action-Concrete-Group G)
      ( X)
      ( Y))
```

### Two equivalences of transitive concrete group actions are homotopic if there exists a point on which they have the same value

```agda
module _
  {l1 l2 l3 : Level} (G : Concrete-Group l1)
  (X : transitive-action-Concrete-Group l2 G)
  (Y : transitive-action-Concrete-Group l3 G)
  (e f : equiv-transitive-action-Concrete-Group G X Y)
  where

  htpy-equiv-transitive-action-Concrete-Group : UU (l2 ⊔ l3)
  htpy-equiv-transitive-action-Concrete-Group =
    htpy-equiv-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group G X)
      ( action-transitive-action-Concrete-Group G Y)
      ( e)
      ( f)

  htpy-prop-equiv-transitive-action-Concrete-Group : Prop (l2 ⊔ l3)
  htpy-prop-equiv-transitive-action-Concrete-Group =
    htpy-prop-equiv-action-Concrete-Group G
      ( action-transitive-action-Concrete-Group G X)
      ( action-transitive-action-Concrete-Group G Y)
      ( e)
      ( f)

  htpy-exists-equiv-transitive-action-Concrete-Group :
    exists-structure
      ( type-transitive-action-Concrete-Group G X)
      ( λ x →
        map-equiv-transitive-action-Concrete-Group G X Y e x ＝
        map-equiv-transitive-action-Concrete-Group G X Y f x) →
    htpy-equiv-transitive-action-Concrete-Group
  htpy-exists-equiv-transitive-action-Concrete-Group H =
    apply-universal-property-trunc-Prop H
      ( htpy-prop-equiv-transitive-action-Concrete-Group)
      ( λ (x , p) y →
        apply-universal-property-trunc-Prop
          ( pr2
            ( is-abstractly-transitive-transitive-action-Concrete-Group G X)
            ( x)
            ( y))
          ( Id-Prop
            ( set-transitive-action-Concrete-Group G Y)
            ( map-equiv-transitive-action-Concrete-Group G X Y e y)
            ( map-equiv-transitive-action-Concrete-Group G X Y f y))
          ( λ (g , q) →
            ( ap (map-equiv-transitive-action-Concrete-Group G X Y e) (inv q)) ∙
            ( preserves-mul-equiv-transitive-action-Concrete-Group
              G X Y e g x) ∙
            ( ap
              ( mul-transitive-action-Concrete-Group G Y g)
              ( p)) ∙
            ( inv
              ( preserves-mul-equiv-transitive-action-Concrete-Group
                G X Y f g x)) ∙
            ( ap (map-equiv-transitive-action-Concrete-Group G X Y f) q)))
```

### The type of transitive concrete group actions is a 1-type

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1)
  where

  is-1-type-transitive-action-Concrete-Group :
    is-1-type (transitive-action-Concrete-Group l2 G)
  is-1-type-transitive-action-Concrete-Group =
    is-1-type-type-subtype
      ( is-transitive-prop-action-Concrete-Group G)
      ( is-1-type-action-Concrete-Group G)

  transitive-action-1-type-Concrete-Group : 1-Type (l1 ⊔ lsuc l2)
  pr1 transitive-action-1-type-Concrete-Group =
    transitive-action-Concrete-Group l2 G
  pr2 transitive-action-1-type-Concrete-Group =
    is-1-type-transitive-action-Concrete-Group
```
