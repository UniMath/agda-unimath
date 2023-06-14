# Transitive concrete group actions

```agda
module group-theory.transitive-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-group-actions
open import group-theory.orbits-concrete-group-actions
```

</details>

## Definition

```agda
is-transitive-action-Concrete-Group-Prop :
  {l1 l2 : Level} (G : Concrete-Group l1) → action-Concrete-Group l2 G →
  Prop (l1 ⊔ l2)
is-transitive-action-Concrete-Group-Prop G X =
  is-0-connected-Prop (orbit-action-Concrete-Group G X)

is-transitive-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) → action-Concrete-Group l2 G →
  UU (l1 ⊔ l2)
is-transitive-action-Concrete-Group G X =
  type-Prop (is-transitive-action-Concrete-Group-Prop G X)

is-prop-is-transitive-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  is-prop (is-transitive-action-Concrete-Group G X)
is-prop-is-transitive-action-Concrete-Group G X =
  is-prop-type-Prop (is-transitive-action-Concrete-Group-Prop G X)

transitive-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
transitive-action-Concrete-Group l2 G =
  type-subtype (is-transitive-action-Concrete-Group-Prop {l2 = l2} G)

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
    apply-universal-property-trunc-Prop
      ( is-inhabited-is-0-connected
        ( is-transitive-transitive-action-Concrete-Group))
      ( is-inhabited-Prop type-transitive-action-Concrete-Group)
      ( λ t →
        apply-universal-property-trunc-Prop
          ( mere-eq-is-0-connected
            ( is-0-connected-classifying-type-Concrete-Group G)
            ( pr1 t)
            ( shape-Concrete-Group G))
          ( is-inhabited-Prop type-transitive-action-Concrete-Group)
          ( λ p →
            unit-trunc-Prop
              ( tr
                ( type-Set ∘ action-transitive-action-Concrete-Group)
                ( p)
                ( pr2 t))))

  mul-transitive-action-Concrete-Group :
    type-Concrete-Group G → type-transitive-action-Concrete-Group →
    type-transitive-action-Concrete-Group
  mul-transitive-action-Concrete-Group =
    mul-action-Concrete-Group G action-transitive-action-Concrete-Group

  is-transitive-mul-transitive-action-Concrete-Group :
    ( x y : type-transitive-action-Concrete-Group) →
    ∃ ( type-Concrete-Group G)
      ( λ g → mul-transitive-action-Concrete-Group g x ＝ y)
  is-transitive-mul-transitive-action-Concrete-Group x y =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected
        ( is-transitive-transitive-action-Concrete-Group)
        ( pair (shape-Concrete-Group G) x)
        ( pair (shape-Concrete-Group G) y))
      ( ∃-Prop
        ( type-Concrete-Group G)
        ( λ g → mul-transitive-action-Concrete-Group g x ＝ y))
      ( λ p → unit-trunc-Prop (pair-eq-Σ p))
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
      ( is-transitive-action-Concrete-Group-Prop G)
      ( X)
      ( Y))
```

## Properties

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

  htpy-equiv-transitive-action-Concrete-Group-Prop : Prop (l2 ⊔ l3)
  htpy-equiv-transitive-action-Concrete-Group-Prop =
    htpy-equiv-action-Concrete-Group-Prop G
      ( action-transitive-action-Concrete-Group G X)
      ( action-transitive-action-Concrete-Group G Y)
      ( e)
      ( f)

  htpy-exists-equiv-transitive-action-Concrete-Group :
    ∃ ( type-transitive-action-Concrete-Group G X)
      ( λ x →
      map-equiv-transitive-action-Concrete-Group G X Y e x ＝
      map-equiv-transitive-action-Concrete-Group G X Y f x) →
    htpy-equiv-transitive-action-Concrete-Group
  htpy-exists-equiv-transitive-action-Concrete-Group H =
    apply-universal-property-trunc-Prop H
      ( htpy-equiv-transitive-action-Concrete-Group-Prop)
      ( λ (pair x p) y →
        apply-universal-property-trunc-Prop
          ( is-transitive-mul-transitive-action-Concrete-Group G X x y)
          ( Id-Prop
            ( set-transitive-action-Concrete-Group G Y)
            ( map-equiv-transitive-action-Concrete-Group G X Y e y)
            ( map-equiv-transitive-action-Concrete-Group G X Y f y))
          ( λ (pair g q) →
            ( ap (map-equiv-transitive-action-Concrete-Group G X Y e) (inv q)) ∙
            ( ( ( preserves-mul-equiv-transitive-action-Concrete-Group
                  G X Y e g x) ∙
                ( ( ap
                    ( mul-transitive-action-Concrete-Group G Y g)
                    ( p)) ∙
                  ( inv
                    ( preserves-mul-equiv-transitive-action-Concrete-Group
                      G X Y f g x)))) ∙
              ( ap (map-equiv-transitive-action-Concrete-Group G X Y f) q))))
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
      ( is-transitive-action-Concrete-Group-Prop G)
      ( is-1-type-action-Concrete-Group G)

  transitive-action-Concrete-Group-1-Type : 1-Type (l1 ⊔ lsuc l2)
  pr1 transitive-action-Concrete-Group-1-Type =
    transitive-action-Concrete-Group l2 G
  pr2 transitive-action-Concrete-Group-1-Type =
    is-1-type-transitive-action-Concrete-Group
```
