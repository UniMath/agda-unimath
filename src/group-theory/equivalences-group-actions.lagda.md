# Equivalences of group actions

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.equivalences-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps funext
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality funext
open import foundation.equivalences funext
open import foundation.functoriality-dependent-function-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.sets funext
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families funext
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.group-actions funext
open import group-theory.groups funext
open import group-theory.homomorphisms-group-actions funext
open import group-theory.homomorphisms-groups funext
open import group-theory.symmetric-groups funext
```

</details>

## Idea

A [morphism of `G`-sets](group-theory.group-actions.md) is said to be an
**equivalence** if its underlying map is an
[equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate of being an equivalence of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  is-equiv-hom-action-Group : hom-action-Group G X Y → UU (l2 ⊔ l3)
  is-equiv-hom-action-Group f = is-equiv (map-hom-action-Group G X Y f)
```

### The type of equivalences of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  equiv-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  equiv-action-Group =
    Σ ( type-action-Group G X ≃ type-action-Group G Y)
      ( λ e →
        ( g : type-Group G) →
        coherence-square-maps
          ( map-equiv e)
          ( mul-action-Group G X g)
          ( mul-action-Group G Y g)
          ( map-equiv e))

  equiv-equiv-action-Group :
    equiv-action-Group → type-action-Group G X ≃ type-action-Group G Y
  equiv-equiv-action-Group = pr1

  map-equiv-action-Group :
    equiv-action-Group → type-action-Group G X → type-action-Group G Y
  map-equiv-action-Group e =
    map-equiv (equiv-equiv-action-Group e)

  is-equiv-map-equiv-action-Group :
    (e : equiv-action-Group) → is-equiv (map-equiv-action-Group e)
  is-equiv-map-equiv-action-Group e =
    is-equiv-map-equiv (equiv-equiv-action-Group e)

  coherence-square-equiv-action-Group :
    (e : equiv-action-Group) (g : type-Group G) →
    coherence-square-maps
      ( map-equiv-action-Group e)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( map-equiv-action-Group e)
  coherence-square-equiv-action-Group = pr2

  hom-equiv-action-Group :
    equiv-action-Group → hom-action-Group G X Y
  pr1 (hom-equiv-action-Group e) = map-equiv-action-Group e
  pr2 (hom-equiv-action-Group e) = coherence-square-equiv-action-Group e

  is-equiv-hom-equiv-action-Group :
    (e : equiv-action-Group) →
    is-equiv-hom-action-Group G X Y (hom-equiv-action-Group e)
  is-equiv-hom-equiv-action-Group =
    is-equiv-map-equiv-action-Group

  equiv-is-equiv-hom-action-Group :
    (f : hom-action-Group G X Y) → is-equiv-hom-action-Group G X Y f →
    equiv-action-Group
  pr1 (pr1 (equiv-is-equiv-hom-action-Group f is-equiv-f)) =
    map-hom-action-Group G X Y f
  pr2 (pr1 (equiv-is-equiv-hom-action-Group f is-equiv-f)) = is-equiv-f
  pr2 (equiv-is-equiv-hom-action-Group f is-equiv-f) =
    preserves-action-hom-action-Group G X Y f
```

### Equality of equivalences of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (e : equiv-action-Group G X Y)
  where

  htpy-equiv-action-Group : (f : equiv-action-Group G X Y) → UU (l2 ⊔ l3)
  htpy-equiv-action-Group f =
    htpy-hom-action-Group G X Y
      ( hom-equiv-action-Group G X Y e)
      ( hom-equiv-action-Group G X Y f)

  refl-htpy-equiv-action-Group : htpy-equiv-action-Group e
  refl-htpy-equiv-action-Group =
    refl-htpy-hom-action-Group G X Y (hom-equiv-action-Group G X Y e)

  htpy-eq-equiv-action-Group :
    (f : equiv-action-Group G X Y) → e ＝ f → htpy-equiv-action-Group f
  htpy-eq-equiv-action-Group .e refl = refl-htpy-equiv-action-Group

  is-torsorial-htpy-equiv-action-Group : is-torsorial htpy-equiv-action-Group
  is-torsorial-htpy-equiv-action-Group =
    is-contr-equiv
      ( Σ ( Σ ( hom-action-Group G X Y) (λ f → is-equiv (pr1 f)))
          ( λ f →
            htpy-hom-action-Group G X Y
              ( hom-equiv-action-Group G X Y e)
              ( pr1 f)))
      ( equiv-Σ
        ( λ f →
          htpy-hom-action-Group G X Y
            ( hom-equiv-action-Group G X Y e)
            ( pr1 f))
        ( equiv-right-swap-Σ)
        ( λ ((f , E) , H) → id-equiv))
      ( is-torsorial-Eq-subtype
        ( is-torsorial-htpy-hom-action-Group G X Y
          ( hom-equiv-action-Group G X Y e))
        ( λ f → is-property-is-equiv (pr1 f))
        ( hom-equiv-action-Group G X Y e)
        ( refl-htpy)
        ( is-equiv-map-equiv (pr1 e)))

  is-equiv-htpy-eq-equiv-action-Group :
    (f : equiv-action-Group G X Y) → is-equiv (htpy-eq-equiv-action-Group f)
  is-equiv-htpy-eq-equiv-action-Group =
    fundamental-theorem-id
      is-torsorial-htpy-equiv-action-Group
      htpy-eq-equiv-action-Group

  extensionality-equiv-action-Group :
    (f : equiv-action-Group G X Y) → (e ＝ f) ≃ htpy-equiv-action-Group f
  pr1 (extensionality-equiv-action-Group f) =
    htpy-eq-equiv-action-Group f
  pr2 (extensionality-equiv-action-Group f) =
    is-equiv-htpy-eq-equiv-action-Group f

  eq-htpy-equiv-action-Group :
    (f : equiv-action-Group G X Y) → htpy-equiv-action-Group f → e ＝ f
  eq-htpy-equiv-action-Group f =
    map-inv-is-equiv (is-equiv-htpy-eq-equiv-action-Group f)
```

### The inverse equivalence of group actions

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  map-inv-equiv-action-Group :
    equiv-action-Group G X Y → type-action-Group G Y → type-action-Group G X
  map-inv-equiv-action-Group e =
    map-inv-equiv (equiv-equiv-action-Group G X Y e)

  preserves-action-map-inv-equiv-action-Group :
    (e : equiv-action-Group G X Y) →
    preserves-action-Group G Y X (map-inv-equiv-action-Group e)
  preserves-action-map-inv-equiv-action-Group (e , H) g =
    horizontal-inv-equiv-coherence-square-maps
      ( e)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( e)
      ( H g)

  inv-equiv-action-Group :
    equiv-action-Group G X Y → equiv-action-Group G Y X
  pr1 (inv-equiv-action-Group (e , H)) = inv-equiv e
  pr2 (inv-equiv-action-Group e) =
    preserves-action-map-inv-equiv-action-Group e

  hom-inv-equiv-action-Group :
    equiv-action-Group G X Y → hom-action-Group G Y X
  hom-inv-equiv-action-Group e =
    hom-equiv-action-Group G Y X (inv-equiv-action-Group e)

module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : hom-action-Group G X Y) (is-equiv-f : is-equiv-hom-action-Group G X Y f)
  where

  map-inv-is-equiv-hom-action-Group :
    type-action-Group G Y → type-action-Group G X
  map-inv-is-equiv-hom-action-Group =
    map-inv-is-equiv is-equiv-f

  preserves-action-map-inv-is-equiv-hom-action-Group :
    preserves-action-Group G Y X (map-inv-is-equiv-hom-action-Group)
  preserves-action-map-inv-is-equiv-hom-action-Group =
    preserves-action-map-inv-equiv-action-Group G X Y
      ( equiv-is-equiv-hom-action-Group G X Y f is-equiv-f)

  hom-inv-is-equiv-hom-action-Group : hom-action-Group G Y X
  hom-inv-is-equiv-hom-action-Group =
    hom-inv-equiv-action-Group G X Y
      ( equiv-is-equiv-hom-action-Group G X Y f is-equiv-f)
```

### The composite of equivalences of group actions

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3) (Z : action-Group G l4)
  where

  comp-equiv-action-Group :
    equiv-action-Group G Y Z → equiv-action-Group G X Y →
    equiv-action-Group G X Z
  pr1 (comp-equiv-action-Group (f , K) (e , H)) = f ∘e e
  pr2 (comp-equiv-action-Group (f , K) (e , H)) g =
    pasting-horizontal-coherence-square-maps
      ( map-equiv e)
      ( map-equiv f)
      ( mul-action-Group G X g)
      ( mul-action-Group G Y g)
      ( mul-action-Group G Z g)
      ( map-equiv e)
      ( map-equiv f)
      ( H g)
      ( K g)
```

### The identity equivalence on group actions

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  id-equiv-action-Group : equiv-action-Group G X X
  pr1 id-equiv-action-Group = id-equiv
  pr2 id-equiv-action-Group g = refl-htpy
```

## Properties

### Equivalences of group actions characterize equality of group actions

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  equiv-eq-action-Group :
    (Y : action-Group G l2) → X ＝ Y → equiv-action-Group G X Y
  equiv-eq-action-Group .X refl = id-equiv-action-Group G X

  abstract
    is-torsorial-equiv-action-Group :
      is-torsorial (λ (Y : action-Group G l2) → equiv-action-Group G X Y)
    is-torsorial-equiv-action-Group =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv-Set (pr1 X))
        ( pr1 X , id-equiv)
        ( is-contr-equiv
          ( Σ ( hom-Group G (symmetric-Group (pr1 X)))
              ( htpy-hom-Group G (symmetric-Group (pr1 X)) (pr2 X)))
          ( equiv-tot
            ( λ f →
              equiv-Π-equiv-family
                ( λ g →
                  inv-equiv
                    ( extensionality-equiv
                      ( map-hom-Group G (symmetric-Group (pr1 X)) (pr2 X) g)
                      ( map-hom-Group G (symmetric-Group (pr1 X)) f g)))))
          ( is-torsorial-htpy-hom-Group G
            ( symmetric-Group (pr1 X))
            ( pr2 X)))

  abstract
    is-equiv-equiv-eq-action-Group :
      (Y : action-Group G l2) → is-equiv (equiv-eq-action-Group Y)
    is-equiv-equiv-eq-action-Group =
      fundamental-theorem-id
        is-torsorial-equiv-action-Group
        equiv-eq-action-Group

  eq-equiv-action-Group :
    (Y : action-Group G l2) → equiv-action-Group G X Y → X ＝ Y
  eq-equiv-action-Group Y =
    map-inv-is-equiv (is-equiv-equiv-eq-action-Group Y)

  extensionality-action-Group :
    (Y : action-Group G l2) → (X ＝ Y) ≃ equiv-action-Group G X Y
  pr1 (extensionality-action-Group Y) =
    equiv-eq-action-Group Y
  pr2 (extensionality-action-Group Y) =
    is-equiv-equiv-eq-action-Group Y
```

### Composition of equivalences of group actions is associative

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1)
  (X1 : action-Group G l2) (X2 : action-Group G l3)
  (X3 : action-Group G l4) (X4 : action-Group G l5)
  where

  associative-comp-equiv-action-Group :
    (h : equiv-action-Group G X3 X4)
    (g : equiv-action-Group G X2 X3)
    (f : equiv-action-Group G X1 X2) →
    comp-equiv-action-Group G X1 X2 X4
      ( comp-equiv-action-Group G X2 X3 X4 h g)
      ( f) ＝
    comp-equiv-action-Group G X1 X3 X4 h
      ( comp-equiv-action-Group G X1 X2 X3 g f)
  associative-comp-equiv-action-Group h g f =
    eq-htpy-equiv-action-Group G X1 X4
      ( comp-equiv-action-Group G X1 X2 X4
        ( comp-equiv-action-Group G X2 X3 X4 h g)
        ( f))
      ( comp-equiv-action-Group G X1 X3 X4 h
        ( comp-equiv-action-Group G X1 X2 X3 g f))
      ( refl-htpy)
```

### The identity equivalence on group actions is a unit of composition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  left-unit-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G X Y Y (id-equiv-action-Group G Y) f ＝ f
  left-unit-law-comp-equiv-action-Group f =
    eq-htpy-equiv-action-Group G X Y
      ( comp-equiv-action-Group G X Y Y (id-equiv-action-Group G Y) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G X X Y f (id-equiv-action-Group G X) ＝ f
  right-unit-law-comp-equiv-action-Group f =
    eq-htpy-equiv-action-Group G X Y
      ( comp-equiv-action-Group G X X Y f (id-equiv-action-Group G X))
      ( f)
      ( refl-htpy)

  left-inverse-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G X Y X (inv-equiv-action-Group G X Y f) f ＝
    id-equiv-action-Group G X
  left-inverse-law-comp-equiv-action-Group f =
    eq-htpy-equiv-action-Group G X X
      ( comp-equiv-action-Group G X Y X (inv-equiv-action-Group G X Y f) f)
      ( id-equiv-action-Group G X)
      ( is-retraction-map-inv-equiv (pr1 f))

  right-inverse-law-comp-equiv-action-Group :
    (f : equiv-action-Group G X Y) →
    comp-equiv-action-Group G Y X Y f (inv-equiv-action-Group G X Y f) ＝
    id-equiv-action-Group G Y
  right-inverse-law-comp-equiv-action-Group f =
    eq-htpy-equiv-action-Group G Y Y
      ( comp-equiv-action-Group G Y X Y f (inv-equiv-action-Group G X Y f))
      ( id-equiv-action-Group G Y)
      ( is-section-map-inv-equiv (pr1 f))
```

## See also

- [Isomorphisms of group actions](group-theory.isomorphisms-group-actions.md)
