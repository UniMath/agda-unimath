---
title: Homomorphisms of group actions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-group-actions where

open import foundation.commuting-squares using
  ( coherence-square; coherence-square-comp-horizontal)
open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_; map-inv-is-equiv)
open import foundation.functions using (id; _∘_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy; is-contr-total-htpy)
open import foundation.identity-types using (Id; refl)
open import foundation.propositions using (is-prop-Π; is-prop-equiv)
open import foundation.sets using (type-Set; is-set-type-Set; is-set; UU-Set)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.group-actions using
  ( Abstract-Group-Action; mul-Abstract-Group-Action;
    set-Abstract-Group-Action; is-set-type-Abstract-Group-Action)
open import group-theory.groups using (Group; type-Group)
```

## Idea

A morphism of group actions from a G-set X to a G-set Y is a map from X to Y preserving the group action.

## Definitions

### Morphisms of G-sets

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  type-hom-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  type-hom-Abstract-Group-Action =
    Σ ( type-Set (pr1 X) → type-Set (pr1 Y))
      ( λ f →
        ( g : type-Group G) →
        coherence-square
          ( f)
          ( mul-Abstract-Group-Action G X g)
          ( mul-Abstract-Group-Action G Y g)
          ( f))

  map-hom-Abstract-Group-Action :
    type-hom-Abstract-Group-Action → type-Set (pr1 X) → type-Set (pr1 Y)
  map-hom-Abstract-Group-Action = pr1

  coherence-square-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action) (g : type-Group G) →
    coherence-square
      ( map-hom-Abstract-Group-Action f)
      ( mul-Abstract-Group-Action G X g)
      ( mul-Abstract-Group-Action G Y g)
      ( map-hom-Abstract-Group-Action f)
  coherence-square-hom-Abstract-Group-Action = pr2
```

### The identity morphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  id-hom-Abstract-Group-Action : type-hom-Abstract-Group-Action G X X
  pr1 id-hom-Abstract-Group-Action = id
  pr2 id-hom-Abstract-Group-Action g = refl-htpy
```

### Composition of morphisms

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (Z : Abstract-Group-Action G l4)
  where

  comp-hom-Abstract-Group-Action :
    type-hom-Abstract-Group-Action G Y Z →
    type-hom-Abstract-Group-Action G X Y →
    type-hom-Abstract-Group-Action G X Z
  pr1 (comp-hom-Abstract-Group-Action (pair g K) (pair f H)) = g ∘ f
  pr2 (comp-hom-Abstract-Group-Action (pair g K) (pair f H)) x =
    coherence-square-comp-horizontal
      ( f)
      ( g)
      ( mul-Abstract-Group-Action G X x)
      ( mul-Abstract-Group-Action G Y x)
      ( mul-Abstract-Group-Action G Z x)
      ( f)
      ( g)
      ( H x)
      ( K x)
```

## Properties

### Equality of homomorphisms of group actions is equivalent to homotopies

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3) (f : type-hom-Abstract-Group-Action G X Y)
  where

  htpy-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) → UU (l2 ⊔ l3)
  htpy-hom-Abstract-Group-Action g = pr1 f ~ pr1 g

  refl-htpy-hom-Abstract-Group-Action : htpy-hom-Abstract-Group-Action f
  refl-htpy-hom-Abstract-Group-Action = refl-htpy

  htpy-eq-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    Id f g → htpy-hom-Abstract-Group-Action g
  htpy-eq-hom-Abstract-Group-Action .f refl =
    refl-htpy-hom-Abstract-Group-Action

  is-contr-total-htpy-hom-Abstract-Group-Action :
    is-contr
      ( Σ ( type-hom-Abstract-Group-Action G X Y)
          ( htpy-hom-Abstract-Group-Action))
  is-contr-total-htpy-hom-Abstract-Group-Action =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (pr1 f))
      ( λ g →
        is-prop-Π
          ( λ x →
            is-prop-Π
              ( λ y →
                is-set-type-Set
                  ( set-Abstract-Group-Action G Y)
                  ( g (mul-Abstract-Group-Action G X x y))
                  ( mul-Abstract-Group-Action G Y x (g y)))))
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    is-equiv (htpy-eq-hom-Abstract-Group-Action g)
  is-equiv-htpy-eq-hom-Abstract-Group-Action =
    fundamental-theorem-id f
      refl-htpy-hom-Abstract-Group-Action
      is-contr-total-htpy-hom-Abstract-Group-Action
      htpy-eq-hom-Abstract-Group-Action

  extensionality-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    Id f g ≃ htpy-hom-Abstract-Group-Action g
  pr1 (extensionality-hom-Abstract-Group-Action g) =
    htpy-eq-hom-Abstract-Group-Action g
  pr2 (extensionality-hom-Abstract-Group-Action g) =
    is-equiv-htpy-eq-hom-Abstract-Group-Action g

  eq-htpy-hom-Abstract-Group-Action :
    (g : type-hom-Abstract-Group-Action G X Y) →
    htpy-hom-Abstract-Group-Action g → Id f g
  eq-htpy-hom-Abstract-Group-Action g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Abstract-Group-Action g)
```

### The type of morphisms of group actions is a set

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where
  
  is-set-type-hom-Abstract-Group-Action :
    is-set (type-hom-Abstract-Group-Action G X Y)
  is-set-type-hom-Abstract-Group-Action f g =
    is-prop-equiv
      ( extensionality-hom-Abstract-Group-Action G X Y f g)
      ( is-prop-Π
        ( λ x →
          is-set-type-Abstract-Group-Action G Y
            ( map-hom-Abstract-Group-Action G X Y f x)
            ( map-hom-Abstract-Group-Action G X Y g x)))

  hom-Abstract-Group-Action : UU-Set (l1 ⊔ l2 ⊔ l3)
  pr1 hom-Abstract-Group-Action = type-hom-Abstract-Group-Action G X Y
  pr2 hom-Abstract-Group-Action = is-set-type-hom-Abstract-Group-Action
```

### Composition is associative

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1) (X1 : Abstract-Group-Action G l2)
  (X2 : Abstract-Group-Action G l3) (X3 : Abstract-Group-Action G l4)
  (X4 : Abstract-Group-Action G l5)
  where

  associative-comp-hom-Abstract-Group-Action :
    (h : type-hom-Abstract-Group-Action G X3 X4)
    (g : type-hom-Abstract-Group-Action G X2 X3)
    (f : type-hom-Abstract-Group-Action G X1 X2) →
    Id ( comp-hom-Abstract-Group-Action G X1 X2 X4
         ( comp-hom-Abstract-Group-Action G X2 X3 X4 h g)
         ( f))
       ( comp-hom-Abstract-Group-Action G X1 X3 X4 h
         ( comp-hom-Abstract-Group-Action G X1 X2 X3 g f))
  associative-comp-hom-Abstract-Group-Action h g f =
    eq-htpy-hom-Abstract-Group-Action G X1 X4
      ( comp-hom-Abstract-Group-Action G X1 X2 X4
        ( comp-hom-Abstract-Group-Action G X2 X3 X4 h g)
        ( f))
      ( comp-hom-Abstract-Group-Action G X1 X3 X4 h
        ( comp-hom-Abstract-Group-Action G X1 X2 X3 g f))
      ( refl-htpy)
```

### Composition satisfies the left and right unit laws

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  left-unit-law-comp-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action G X Y) →
    Id ( comp-hom-Abstract-Group-Action G X Y Y
         ( id-hom-Abstract-Group-Action G Y)
         ( f))
       ( f)
  left-unit-law-comp-hom-Abstract-Group-Action f =
    eq-htpy-hom-Abstract-Group-Action G X Y
      ( comp-hom-Abstract-Group-Action G X Y Y
        ( id-hom-Abstract-Group-Action G Y)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-Abstract-Group-Action :
    (f : type-hom-Abstract-Group-Action G X Y) →
    Id ( comp-hom-Abstract-Group-Action G X X Y f
         ( id-hom-Abstract-Group-Action G X))
       ( f)
  right-unit-law-comp-hom-Abstract-Group-Action f =
    eq-htpy-hom-Abstract-Group-Action G X Y
      ( comp-hom-Abstract-Group-Action G X X Y f
        ( id-hom-Abstract-Group-Action G X))
      ( f)
      ( refl-htpy)
```
