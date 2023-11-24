# Equivalences of concrete group actions

```agda
module group-theory.equivalences-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.homomorphisms-concrete-group-actions
```

</details>

## Idea

An equivalence of concrete group actions from `X` to `Y` is a family of
equivalences from `X u` to `Y u` indexed by `u : BG`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  equiv-action-Concrete-Group :
    {l3 : Level} (Y : action-Concrete-Group l3 G) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-action-Concrete-Group Y =
    (u : classifying-type-Concrete-Group G) → type-equiv-Set (X u) (Y u)

  id-equiv-action-Concrete-Group : equiv-action-Concrete-Group X
  id-equiv-action-Concrete-Group u = id-equiv

  extensionality-action-Concrete-Group :
    (Y : action-Concrete-Group l2 G) → (X ＝ Y) ≃ equiv-action-Concrete-Group Y
  extensionality-action-Concrete-Group =
    extensionality-Π X
      ( λ u → type-equiv-Set (X u))
      ( λ u → extensionality-Set (X u))

  equiv-eq-action-Concrete-Group :
    (Y : action-Concrete-Group l2 G) → (X ＝ Y) → equiv-action-Concrete-Group Y
  equiv-eq-action-Concrete-Group Y =
    map-equiv (extensionality-action-Concrete-Group Y)

  eq-equiv-action-Concrete-Group :
    (Y : action-Concrete-Group l2 G) → equiv-action-Concrete-Group Y → (X ＝ Y)
  eq-equiv-action-Concrete-Group Y =
    map-inv-equiv (extensionality-action-Concrete-Group Y)

  is-torsorial-equiv-action-Concrete-Group :
    is-torsorial equiv-action-Concrete-Group
  is-torsorial-equiv-action-Concrete-Group =
    is-torsorial-Eq-Π
      ( λ u → type-equiv-Set (X u))
      ( λ u → is-torsorial-equiv-Set (X u))

module _
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  (Y : action-Concrete-Group l3 G)
  where

  emb-hom-equiv-action-Concrete-Group :
    equiv-action-Concrete-Group G X Y ↪ hom-action-Concrete-Group G X Y
  emb-hom-equiv-action-Concrete-Group = emb-Π (λ u → emb-map-equiv)

  hom-equiv-action-Concrete-Group :
    equiv-action-Concrete-Group G X Y → hom-action-Concrete-Group G X Y
  hom-equiv-action-Concrete-Group = map-emb emb-hom-equiv-action-Concrete-Group

  is-emb-hom-equiv-action-Concrete-Group :
    is-emb hom-equiv-action-Concrete-Group
  is-emb-hom-equiv-action-Concrete-Group =
    is-emb-map-emb emb-hom-equiv-action-Concrete-Group

  map-equiv-action-Concrete-Group :
    equiv-action-Concrete-Group G X Y →
    type-action-Concrete-Group G X → type-action-Concrete-Group G Y
  map-equiv-action-Concrete-Group e =
    map-hom-action-Concrete-Group G X Y (hom-equiv-action-Concrete-Group e)

  preserves-mul-equiv-action-Concrete-Group :
    (e : equiv-action-Concrete-Group G X Y) (g : type-Concrete-Group G)
    (x : type-action-Concrete-Group G X) →
    ( map-equiv-action-Concrete-Group e (mul-action-Concrete-Group G X g x)) ＝
    ( mul-action-Concrete-Group G Y g (map-equiv-action-Concrete-Group e x))
  preserves-mul-equiv-action-Concrete-Group e =
    preserves-mul-hom-action-Concrete-Group G X Y
      ( hom-equiv-action-Concrete-Group e)

  htpy-equiv-action-Concrete-Group :
    (e f : equiv-action-Concrete-Group G X Y) → UU (l2 ⊔ l3)
  htpy-equiv-action-Concrete-Group e f =
    htpy-hom-action-Concrete-Group G X Y
      ( hom-equiv-action-Concrete-Group e)
      ( hom-equiv-action-Concrete-Group f)

  extensionality-equiv-action-Concrete-Group :
    (e f : equiv-action-Concrete-Group G X Y) →
    (e ＝ f) ≃ htpy-equiv-action-Concrete-Group e f
  extensionality-equiv-action-Concrete-Group e f =
    ( extensionality-hom-action-Concrete-Group G X Y
      ( hom-equiv-action-Concrete-Group e)
      ( hom-equiv-action-Concrete-Group f)) ∘e
    ( equiv-ap-emb emb-hom-equiv-action-Concrete-Group)

  eq-htpy-equiv-action-Concrete-Group :
    (e f : equiv-action-Concrete-Group G X Y) →
    htpy-equiv-action-Concrete-Group e f → (e ＝ f)
  eq-htpy-equiv-action-Concrete-Group e f =
    map-inv-equiv (extensionality-equiv-action-Concrete-Group e f)
```

## Properties

### The type of equivalences between concrete group actions is a set

```agda
module _
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  (Y : action-Concrete-Group l3 G)
  where

  is-prop-htpy-equiv-action-Concrete-Group :
    (e f : equiv-action-Concrete-Group G X Y) →
    is-prop (htpy-equiv-action-Concrete-Group G X Y e f)
  is-prop-htpy-equiv-action-Concrete-Group e f =
    is-prop-htpy-hom-action-Concrete-Group G X Y
      ( hom-equiv-action-Concrete-Group G X Y e)
      ( hom-equiv-action-Concrete-Group G X Y f)

  htpy-prop-equiv-action-Concrete-Group :
    (e f : equiv-action-Concrete-Group G X Y) → Prop (l2 ⊔ l3)
  pr1 (htpy-prop-equiv-action-Concrete-Group e f) =
    htpy-equiv-action-Concrete-Group G X Y e f
  pr2 (htpy-prop-equiv-action-Concrete-Group e f) =
    is-prop-htpy-equiv-action-Concrete-Group e f

  is-set-equiv-action-Concrete-Group :
    is-set (equiv-action-Concrete-Group G X Y)
  is-set-equiv-action-Concrete-Group e f =
    is-prop-equiv
      ( extensionality-equiv-action-Concrete-Group G X Y e f)
      ( is-prop-htpy-equiv-action-Concrete-Group e f)
```

### The type of concrete group actions is a 1-type

```agda
is-1-type-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) →
  is-1-type (action-Concrete-Group l2 G)
is-1-type-action-Concrete-Group G X Y =
  is-set-equiv
    ( equiv-action-Concrete-Group G X Y)
    ( extensionality-action-Concrete-Group G X Y)
    ( is-set-equiv-action-Concrete-Group G X Y)
```
