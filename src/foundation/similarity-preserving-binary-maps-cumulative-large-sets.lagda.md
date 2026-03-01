# Similarity preserving binary maps on cumulative large sets

```agda
module foundation.similarity-preserving-binary-maps-cumulative-large-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.identity-types
open import foundation.similarity-preserving-binary-maps-large-similarity-relations
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-large-similarity-relations
open import foundation.universe-levels
```

</details>

## Idea

Given [cumulative large sets](foundation.cumulative-large-sets.md) `X Y Z`, a
binary map `f : X → Y → Z`
{{#concept "preserves similarity" Disambiguation="binary maps over cumulative large sets" Agda=preserves-sim-binary-map-Cumulative-Large-Set}}
if whenever `x` is similar to `x'` and `y` is similar to `y'`, `f x y` is
similar to `f x' y'`.

## Definition

```agda
module _
  {αX αY αZ : Level → Level}
  {βX βY βZ : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  (SZ : Cumulative-Large-Set αZ βZ)
  where

  preserves-sim-binary-map-Cumulative-Large-Set :
    ( {l1 l2 : Level} →
      type-Cumulative-Large-Set SX l1 →
      type-Cumulative-Large-Set SY l2 →
      type-Cumulative-Large-Set SZ (l1 ⊔ l2)) →
    UUω
  preserves-sim-binary-map-Cumulative-Large-Set f =
    preserves-sim-binary-map-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set SX)
      ( large-similarity-relation-Cumulative-Large-Set SY)
      ( large-similarity-relation-Cumulative-Large-Set SZ)
      ( f)

  sim-preserving-binary-map-Cumulative-Large-Set : UUω
  sim-preserving-binary-map-Cumulative-Large-Set =
    sim-preserving-binary-map-Large-Similarity-Relation
      ( large-similarity-relation-Cumulative-Large-Set SX)
      ( large-similarity-relation-Cumulative-Large-Set SY)
      ( large-similarity-relation-Cumulative-Large-Set SZ)

  map-sim-preserving-binary-map-Cumulative-Large-Set :
    sim-preserving-binary-map-Cumulative-Large-Set →
    {l1 l2 : Level} →
    type-Cumulative-Large-Set SX l1 →
    type-Cumulative-Large-Set SY l2 →
    type-Cumulative-Large-Set SZ (l1 ⊔ l2)
  map-sim-preserving-binary-map-Cumulative-Large-Set =
    map-sim-preserving-binary-map-Large-Similarity-Relation

  preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set :
    (f : sim-preserving-binary-map-Cumulative-Large-Set) →
    preserves-sim-binary-map-Cumulative-Large-Set
      ( map-sim-preserving-binary-map-Cumulative-Large-Set f)
  preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set =
    preserves-sim-map-sim-preserving-binary-map-Large-Similarity-Relation
```

### Similarity preserving binary operators

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  where

  preserves-sim-binary-operator-Cumulative-Large-Set :
    ( {l1 l2 : Level} →
      type-Cumulative-Large-Set S l1 →
      type-Cumulative-Large-Set S l2 →
      type-Cumulative-Large-Set S (l1 ⊔ l2)) →
    UUω
  preserves-sim-binary-operator-Cumulative-Large-Set =
    preserves-sim-binary-map-Cumulative-Large-Set S S S

  sim-preserving-binary-operator-Cumulative-Large-Set : UUω
  sim-preserving-binary-operator-Cumulative-Large-Set =
    sim-preserving-binary-map-Cumulative-Large-Set S S S

  map-sim-preserving-binary-operator-Cumulative-Large-Set :
    sim-preserving-binary-operator-Cumulative-Large-Set →
    {l1 l2 : Level} →
    type-Cumulative-Large-Set S l1 →
    type-Cumulative-Large-Set S l2 →
    type-Cumulative-Large-Set S (l1 ⊔ l2)
  map-sim-preserving-binary-operator-Cumulative-Large-Set =
    map-sim-preserving-binary-map-Large-Similarity-Relation

  preserves-sim-map-sim-preserving-binary-operator-Cumulative-Large-Set :
    (f : sim-preserving-binary-operator-Cumulative-Large-Set) →
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( map-sim-preserving-binary-operator-Cumulative-Large-Set f)
  preserves-sim-map-sim-preserving-binary-operator-Cumulative-Large-Set =
    preserves-sim-map-sim-preserving-binary-map-Large-Similarity-Relation
```

## Properties

### Raising universe levels on similarity preserving binary maps

```agda
module _
  {αX αY αZ : Level → Level}
  {βX βY βZ : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  (SZ : Cumulative-Large-Set αZ βZ)
  where

  abstract
    map-raise-left-preserves-sim-binary-map-Cumulative-Large-Set :
      (f :
        {l1 l2 : Level} →
        type-Cumulative-Large-Set SX l1 →
        type-Cumulative-Large-Set SY l2 →
        type-Cumulative-Large-Set SZ (l1 ⊔ l2)) →
      preserves-sim-binary-map-Cumulative-Large-Set SX SY SZ f →
      {l1 l2 : Level} (l3 : Level)
      (x : type-Cumulative-Large-Set SX l1)
      (y : type-Cumulative-Large-Set SY l2) →
      f (raise-Cumulative-Large-Set SX l3 x) y ＝
      raise-Cumulative-Large-Set SZ l3 (f x y)
    map-raise-left-preserves-sim-binary-map-Cumulative-Large-Set
      f preserves-sim-f l3 x y =
      eq-sim-Cumulative-Large-Set SZ _ _
        ( transitive-sim-Cumulative-Large-Set SZ _ _ _
          ( sim-raise-Cumulative-Large-Set SZ l3 (f x y))
          ( preserves-sim-f _ _ _ _
            ( sim-raise-Cumulative-Large-Set' SX l3 x)
            ( refl-sim-Cumulative-Large-Set SY y)))

    map-raise-right-preserves-sim-binary-map-Cumulative-Large-Set :
      (f :
        {l1 l2 : Level} →
        type-Cumulative-Large-Set SX l1 →
        type-Cumulative-Large-Set SY l2 →
        type-Cumulative-Large-Set SZ (l1 ⊔ l2)) →
      preserves-sim-binary-map-Cumulative-Large-Set SX SY SZ f →
      {l1 l2 : Level} (l3 : Level)
      (x : type-Cumulative-Large-Set SX l1)
      (y : type-Cumulative-Large-Set SY l2) →
      f x (raise-Cumulative-Large-Set SY l3 y) ＝
      raise-Cumulative-Large-Set SZ l3 (f x y)
    map-raise-right-preserves-sim-binary-map-Cumulative-Large-Set
      f preserves-sim-f l3 x y =
      eq-sim-Cumulative-Large-Set SZ _ _
        ( transitive-sim-Cumulative-Large-Set SZ _ _ _
          ( sim-raise-Cumulative-Large-Set SZ l3 (f x y))
          ( preserves-sim-f _ _ _ _
            ( refl-sim-Cumulative-Large-Set SX x)
            ( sim-raise-Cumulative-Large-Set' SY l3 y)))

    map-raise-raise-preserves-sim-binary-map-Cumulative-Large-Set :
      (f :
        {l1 l2 : Level} →
        type-Cumulative-Large-Set SX l1 →
        type-Cumulative-Large-Set SY l2 →
        type-Cumulative-Large-Set SZ (l1 ⊔ l2)) →
      preserves-sim-binary-map-Cumulative-Large-Set SX SY SZ f →
      {l1 l2 : Level} (l3 l4 : Level)
      (x : type-Cumulative-Large-Set SX l1)
      (y : type-Cumulative-Large-Set SY l2) →
      f
        ( raise-Cumulative-Large-Set SX l3 x)
        ( raise-Cumulative-Large-Set SY l4 y) ＝
      raise-Cumulative-Large-Set SZ (l3 ⊔ l4) (f x y)
    map-raise-raise-preserves-sim-binary-map-Cumulative-Large-Set
      f preserves-sim-f l3 l4 x y =
      eq-sim-Cumulative-Large-Set SZ _ _
        ( transitive-sim-Cumulative-Large-Set SZ _ _ _
          ( sim-raise-Cumulative-Large-Set SZ (l3 ⊔ l4) (f x y))
          ( preserves-sim-f _ _ _ _
            ( sim-raise-Cumulative-Large-Set' SX l3 x)
            ( sim-raise-Cumulative-Large-Set' SY l4 y)))

module _
  {αX αY αZ : Level → Level}
  {βX βY βZ : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  (SZ : Cumulative-Large-Set αZ βZ)
  (f : sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ)
  where

  abstract
    map-raise-left-sim-preserving-binary-map-Cumulative-Large-Set :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Cumulative-Large-Set SX l1)
      (y : type-Cumulative-Large-Set SY l2) →
      map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ
        ( f)
        ( raise-Cumulative-Large-Set SX l3 x)
        ( y) ＝
      raise-Cumulative-Large-Set SZ
        ( l3)
        ( map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f x y)
    map-raise-left-sim-preserving-binary-map-Cumulative-Large-Set =
      map-raise-left-preserves-sim-binary-map-Cumulative-Large-Set SX SY SZ
        ( map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f)
        ( preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set
          ( SX)
          ( SY)
          ( SZ)
          ( f))

    map-raise-right-sim-preserving-binary-map-Cumulative-Large-Set :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Cumulative-Large-Set SX l1)
      (y : type-Cumulative-Large-Set SY l2) →
      map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ
        ( f)
        ( x)
        ( raise-Cumulative-Large-Set SY l3 y) ＝
      raise-Cumulative-Large-Set SZ
        ( l3)
        ( map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f x y)
    map-raise-right-sim-preserving-binary-map-Cumulative-Large-Set =
      map-raise-right-preserves-sim-binary-map-Cumulative-Large-Set SX SY SZ
        ( map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f)
        ( preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set
          ( SX)
          ( SY)
          ( SZ)
          ( f))

    map-raise-raise-sim-preserving-binary-map-Cumulative-Large-Set :
      {l1 l2 : Level} (l3 l4 : Level)
      (x : type-Cumulative-Large-Set SX l1)
      (y : type-Cumulative-Large-Set SY l2) →
      map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ
        ( f)
        ( raise-Cumulative-Large-Set SX l3 x)
        ( raise-Cumulative-Large-Set SY l4 y) ＝
      raise-Cumulative-Large-Set SZ
        ( l3 ⊔ l4)
        ( map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f x y)
    map-raise-raise-sim-preserving-binary-map-Cumulative-Large-Set =
      map-raise-raise-preserves-sim-binary-map-Cumulative-Large-Set SX SY SZ
        ( map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f)
        ( preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set
          ( SX)
          ( SY)
          ( SZ)
          ( f))

module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  (f : sim-preserving-binary-operator-Cumulative-Large-Set S)
  where

  abstract
    map-raise-left-sim-preserving-binary-operator-Cumulative-Large-Set :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Cumulative-Large-Set S l1)
      (y : type-Cumulative-Large-Set S l2) →
      map-sim-preserving-binary-operator-Cumulative-Large-Set S
        ( f)
        ( raise-Cumulative-Large-Set S l3 x)
        ( y) ＝
      raise-Cumulative-Large-Set S
        ( l3)
        ( map-sim-preserving-binary-operator-Cumulative-Large-Set S f x y)
    map-raise-left-sim-preserving-binary-operator-Cumulative-Large-Set =
      map-raise-left-sim-preserving-binary-map-Cumulative-Large-Set S S S f

    map-raise-right-sim-preserving-binary-operator-Cumulative-Large-Set :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Cumulative-Large-Set S l1)
      (y : type-Cumulative-Large-Set S l2) →
      map-sim-preserving-binary-operator-Cumulative-Large-Set S
        ( f)
        ( x)
        ( raise-Cumulative-Large-Set S l3 y) ＝
      raise-Cumulative-Large-Set S
        ( l3)
        ( map-sim-preserving-binary-operator-Cumulative-Large-Set S f x y)
    map-raise-right-sim-preserving-binary-operator-Cumulative-Large-Set =
      map-raise-right-sim-preserving-binary-map-Cumulative-Large-Set S S S f

    map-raise-raise-sim-preserving-binary-operator-Cumulative-Large-Set :
      {l1 l2 : Level} (l3 l4 : Level)
      (x : type-Cumulative-Large-Set S l1)
      (y : type-Cumulative-Large-Set S l2) →
      map-sim-preserving-binary-operator-Cumulative-Large-Set S
        ( f)
        ( raise-Cumulative-Large-Set S l3 x)
        ( raise-Cumulative-Large-Set S l4 y) ＝
      raise-Cumulative-Large-Set S
        ( l3 ⊔ l4)
        ( map-sim-preserving-binary-operator-Cumulative-Large-Set S f x y)
    map-raise-raise-sim-preserving-binary-operator-Cumulative-Large-Set =
      map-raise-raise-sim-preserving-binary-map-Cumulative-Large-Set S S S f
```

### A similarity-preserving binary map preserves similarity on the left and right

```agda
module _
  {αX αY αZ : Level → Level}
  {βX βY βZ : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  (SZ : Cumulative-Large-Set αZ βZ)
  (f : sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ)
  where

  preserves-sim-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set :
    {l : Level} (x : type-Cumulative-Large-Set SX l) →
    preserves-sim-map-Cumulative-Large-Set
      ( l ⊔_)
      ( SY)
      ( SZ)
      ( map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f x)
  preserves-sim-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set
    x y y' =
    preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set
      ( SX)
      ( SY)
      ( SZ)
      ( f)
      ( x)
      ( x)
      ( y)
      ( y')
      ( refl-sim-Cumulative-Large-Set SX x)

  sim-preserving-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set :
    {l : Level} (x : type-Cumulative-Large-Set SX l) →
    sim-preserving-map-Cumulative-Large-Set (l ⊔_) SY SZ
  sim-preserving-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set x =
    λ where
      .map-sim-preserving-map-Large-Similarity-Relation →
        map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f x
      .preserves-sim-map-sim-preserving-map-Large-Similarity-Relation →
        preserves-sim-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set
          ( x)

  preserves-sim-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set :
    {l : Level} (y : type-Cumulative-Large-Set SY l) →
    preserves-sim-map-Cumulative-Large-Set
      ( l ⊔_)
      ( SX)
      ( SZ)
      ( λ x → map-sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ f x y)
  preserves-sim-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set
    y x x' x~x' =
    preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set
      ( SX)
      ( SY)
      ( SZ)
      ( f)
      ( x)
      ( x')
      ( y)
      ( y)
      ( x~x')
      ( refl-sim-Cumulative-Large-Set SY y)

  sim-preserving-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set :
    {l : Level} (y : type-Cumulative-Large-Set SY l) →
    sim-preserving-map-Cumulative-Large-Set (l ⊔_) SX SZ
  sim-preserving-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set y =
    λ where
      .map-sim-preserving-map-Large-Similarity-Relation x →
        map-sim-preserving-binary-map-Large-Similarity-Relation f x y
      .preserves-sim-map-sim-preserving-map-Large-Similarity-Relation →
        preserves-sim-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set
          ( y)

module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (S : Cumulative-Large-Set α β)
  (f : sim-preserving-binary-operator-Cumulative-Large-Set S)
  where

  preserves-sim-map-ev-right-sim-preserving-binary-operator-Cumulative-Large-Set :
    {l : Level} (x : type-Cumulative-Large-Set S l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( S)
      ( map-sim-preserving-binary-operator-Cumulative-Large-Set S f x)
  preserves-sim-map-ev-right-sim-preserving-binary-operator-Cumulative-Large-Set =
    preserves-sim-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set
      ( S)
      ( S)
      ( S)
      ( f)

  sim-preserving-endomap-ev-right-sim-preserving-binary-operator-Cumulative-Large-Set :
    {l : Level} (x : type-Cumulative-Large-Set S l) →
    sim-preserving-endomap-Cumulative-Large-Set (l ⊔_) S
  sim-preserving-endomap-ev-right-sim-preserving-binary-operator-Cumulative-Large-Set =
    sim-preserving-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set
      ( S)
      ( S)
      ( S)
      ( f)

  preserves-sim-map-ev-left-sim-preserving-binary-operator-Cumulative-Large-Set :
    {l : Level} (y : type-Cumulative-Large-Set S l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( S)
      ( λ x → map-sim-preserving-binary-operator-Cumulative-Large-Set S f x y)
  preserves-sim-map-ev-left-sim-preserving-binary-operator-Cumulative-Large-Set =
    preserves-sim-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set
      ( S)
      ( S)
      ( S)
      ( f)

  sim-preserving-endomap-ev-left-sim-preserving-binary-operator-Cumulative-Large-Set :
    {l : Level} (y : type-Cumulative-Large-Set S l) →
    sim-preserving-endomap-Cumulative-Large-Set (l ⊔_) S
  sim-preserving-endomap-ev-left-sim-preserving-binary-operator-Cumulative-Large-Set =
    sim-preserving-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set
      ( S)
      ( S)
      ( S)
      ( f)
```

### Constructing similarity-preserving binary maps

```agda
module _
  {αX αY αZ : Level → Level}
  {βX βY βZ : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  (SY : Cumulative-Large-Set αY βY)
  (SZ : Cumulative-Large-Set αZ βZ)
  where

  make-sim-preserving-binary-map-Cumulative-Large-Set :
    (f :
      {l1 l2 : Level} →
      type-Cumulative-Large-Set SX l1 → type-Cumulative-Large-Set SY l2 →
      type-Cumulative-Large-Set SZ (l1 ⊔ l2)) →
    preserves-sim-binary-map-Cumulative-Large-Set SX SY SZ f →
    sim-preserving-binary-map-Cumulative-Large-Set SX SY SZ
  make-sim-preserving-binary-map-Cumulative-Large-Set f preserves-sim-f =
    λ where
      .map-sim-preserving-binary-map-Large-Similarity-Relation →
        f
      .preserves-sim-map-sim-preserving-binary-map-Large-Similarity-Relation →
        preserves-sim-f

module _
  {αX : Level → Level}
  {βX : Level → Level → Level}
  (SX : Cumulative-Large-Set αX βX)
  where

  make-sim-preserving-binary-operator-Cumulative-Large-Set :
    (f :
      {l1 l2 : Level} →
      type-Cumulative-Large-Set SX l1 → type-Cumulative-Large-Set SX l2 →
      type-Cumulative-Large-Set SX (l1 ⊔ l2)) →
    preserves-sim-binary-operator-Cumulative-Large-Set SX f →
    sim-preserving-binary-operator-Cumulative-Large-Set SX
  make-sim-preserving-binary-operator-Cumulative-Large-Set =
    make-sim-preserving-binary-map-Cumulative-Large-Set SX SX SX
```
