# Large precategories

```agda
module category-theory.large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

A **large precategory** is a [precategory](category-theory.precategories.md)
where we don't fix a universe for the type of objects or morphisms. (This cannot
be done with Σ-types, we must use a record type.)

## Definition

### The large type of large precategories

```agda
record
  Large-Precategory (α : Level → Level) (β : Level → Level → Level) : UUω where

  eta-equality

  field
    obj-Large-Precategory :
      (l : Level) → UU (α l)

    hom-set-Large-Precategory :
      {l1 l2 : Level} →
      obj-Large-Precategory l1 →
      obj-Large-Precategory l2 →
      Set (β l1 l2)

  hom-Large-Precategory :
    {l1 l2 : Level} →
    obj-Large-Precategory l1 →
    obj-Large-Precategory l2 →
    UU (β l1 l2)
  hom-Large-Precategory X Y = type-Set (hom-set-Large-Precategory X Y)

  is-set-hom-Large-Precategory :
    {l1 l2 : Level}
    (X : obj-Large-Precategory l1)
    (Y : obj-Large-Precategory l2) →
    is-set (hom-Large-Precategory X Y)
  is-set-hom-Large-Precategory X Y =
    is-set-type-Set (hom-set-Large-Precategory X Y)

  field
    comp-hom-Large-Precategory :
      {l1 l2 l3 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      {Z : obj-Large-Precategory l3} →
      hom-Large-Precategory Y Z →
      hom-Large-Precategory X Y →
      hom-Large-Precategory X Z

    id-hom-Large-Precategory :
      {l1 : Level}
      {X : obj-Large-Precategory l1} →
      hom-Large-Precategory X X

    involutive-eq-associative-comp-hom-Large-Precategory :
      {l1 l2 l3 l4 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      {Z : obj-Large-Precategory l3}
      {W : obj-Large-Precategory l4} →
      (h : hom-Large-Precategory Z W)
      (g : hom-Large-Precategory Y Z)
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory (comp-hom-Large-Precategory h g) f) ＝ⁱ
      ( comp-hom-Large-Precategory h (comp-hom-Large-Precategory g f))

    left-unit-law-comp-hom-Large-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory id-hom-Large-Precategory f) ＝ f

    right-unit-law-comp-hom-Large-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory f id-hom-Large-Precategory) ＝ f

  associative-comp-hom-Large-Precategory :
      {l1 l2 l3 l4 : Level}
      {X : obj-Large-Precategory l1}
      {Y : obj-Large-Precategory l2}
      {Z : obj-Large-Precategory l3}
      {W : obj-Large-Precategory l4} →
      (h : hom-Large-Precategory Z W)
      (g : hom-Large-Precategory Y Z)
      (f : hom-Large-Precategory X Y) →
      ( comp-hom-Large-Precategory (comp-hom-Large-Precategory h g) f) ＝
      ( comp-hom-Large-Precategory h (comp-hom-Large-Precategory g f))
  associative-comp-hom-Large-Precategory h g f =
    eq-involutive-eq
      ( involutive-eq-associative-comp-hom-Large-Precategory h g f)

open Large-Precategory public

make-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level}
  ( obj : (l : Level) → UU (α l))
  ( hom-set : {l1 l2 : Level} → obj l1 → obj l2 → Set (β l1 l2))
  ( _∘_ :
    {l1 l2 l3 : Level}
    {X : obj l1} {Y : obj l2} {Z : obj l3} →
    type-Set (hom-set Y Z) → type-Set (hom-set X Y) → type-Set (hom-set X Z))
  ( id : {l : Level} {X : obj l} → type-Set (hom-set X X))
  ( assoc-comp-hom :
    {l1 l2 l3 l4 : Level}
    {X : obj l1} {Y : obj l2} {Z : obj l3} {W : obj l4}
    (h : type-Set (hom-set Z W))
    (g : type-Set (hom-set Y Z))
    (f : type-Set (hom-set X Y)) →
    ( (h ∘ g) ∘ f) ＝ ( h ∘ (g ∘ f)))
  ( left-unit-comp-hom :
    {l1 l2 : Level} {X : obj l1} {Y : obj l2} (f : type-Set (hom-set X Y)) →
    id ∘ f ＝ f)
  ( right-unit-comp-hom :
    {l1 l2 : Level} {X : obj l1} {Y : obj l2} (f : type-Set (hom-set X Y)) →
    f ∘ id ＝ f) →
  Large-Precategory α β
make-Large-Precategory
  obj hom-set _∘_ id assoc-comp-hom left-unit-comp-hom right-unit-comp-hom =
  λ where
    .obj-Large-Precategory → obj
    .hom-set-Large-Precategory → hom-set
    .comp-hom-Large-Precategory → _∘_
    .id-hom-Large-Precategory → id
    .involutive-eq-associative-comp-hom-Large-Precategory h g f →
      involutive-eq-eq (assoc-comp-hom h g f)
    .left-unit-law-comp-hom-Large-Precategory → left-unit-comp-hom
    .right-unit-law-comp-hom-Large-Precategory → right-unit-comp-hom

{-# INLINE make-Large-Precategory #-}
```

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (C : Large-Precategory α β)
  where

  ap-comp-hom-Large-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    {Z : obj-Large-Precategory C l3}
    {g g' : hom-Large-Precategory C Y Z} (p : g ＝ g')
    {f f' : hom-Large-Precategory C X Y} (q : f ＝ f') →
    comp-hom-Large-Precategory C g f ＝
    comp-hom-Large-Precategory C g' f'
  ap-comp-hom-Large-Precategory = ap-binary (comp-hom-Large-Precategory C)

  comp-hom-Large-Precategory' :
    {l1 l2 l3 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    {Z : obj-Large-Precategory C l3} →
    hom-Large-Precategory C X Y →
    hom-Large-Precategory C Y Z →
    hom-Large-Precategory C X Z
  comp-hom-Large-Precategory' f g = comp-hom-Large-Precategory C g f
```

### Precategories obtained from large precategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  where

  precategory-Large-Precategory :
    (l : Level) → Precategory (α l) (β l l)
  pr1 (precategory-Large-Precategory l) =
    obj-Large-Precategory C l
  pr1 (pr2 (precategory-Large-Precategory l)) =
    hom-set-Large-Precategory C
  pr1 (pr1 (pr2 (pr2 (precategory-Large-Precategory l)))) =
    comp-hom-Large-Precategory C
  pr2 (pr1 (pr2 (pr2 (precategory-Large-Precategory l)))) =
    involutive-eq-associative-comp-hom-Large-Precategory C
  pr1 (pr2 (pr2 (pr2 (precategory-Large-Precategory l)))) x =
    id-hom-Large-Precategory C
  pr1 (pr2 (pr2 (pr2 (pr2 (precategory-Large-Precategory l))))) =
    left-unit-law-comp-hom-Large-Precategory C
  pr2 (pr2 (pr2 (pr2 (pr2 (precategory-Large-Precategory l))))) =
    right-unit-law-comp-hom-Large-Precategory C
```

### Equalities induce morphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  {l1 : Level}
  where

  hom-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) → X ＝ Y → hom-Large-Precategory C X Y
  hom-eq-Large-Precategory X .X refl = id-hom-Large-Precategory C

  hom-inv-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) → X ＝ Y → hom-Large-Precategory C Y X
  hom-inv-eq-Large-Precategory X Y = hom-eq-Large-Precategory Y X ∘ inv

  compute-hom-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) →
    hom-eq-Precategory (precategory-Large-Precategory C l1) X Y ~
    hom-eq-Large-Precategory X Y
  compute-hom-eq-Large-Precategory X .X refl = refl
```

### Pre- and postcomposition by a morphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  where

  precomp-hom-Large-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-Large-Precategory C l1}
    {Y : obj-Large-Precategory C l2}
    (f : hom-Large-Precategory C X Y) →
    (Z : obj-Large-Precategory C l3) →
    hom-Large-Precategory C Y Z → hom-Large-Precategory C X Z
  precomp-hom-Large-Precategory f Z g =
    comp-hom-Large-Precategory C g f

  postcomp-hom-Large-Precategory :
    {l1 l2 l3 : Level}
    (X : obj-Large-Precategory C l1)
    {Y : obj-Large-Precategory C l2}
    {Z : obj-Large-Precategory C l3}
    (f : hom-Large-Precategory C Y Z) →
    hom-Large-Precategory C X Y → hom-Large-Precategory C X Z
  postcomp-hom-Large-Precategory X f g =
    comp-hom-Large-Precategory C f g
```
