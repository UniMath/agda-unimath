# Large wild 1-precategories

```agda
module wild-category-theory.large-wild-1-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.contratransitive-binary-relations
open import foundation.dependent-pair-types
open import foundation.strict-symmetrization-binary-relations
open import foundation.universe-levels

open import wild-category-theory.large-wild-0-1-precategories
open import wild-category-theory.strict-symmetrization-wild-0-pregroupoid-relations
open import wild-category-theory.wild-0-pregroupoid-relations
```

</details>

## Idea

A {{#concept "large wild 1-precategory" }} is...

## Definitions

### Large wild 1-precategories

```agda
record
  Large-Wild-1-Precategory
    (α : Level → Level)
    (β : Level → Level → Level)
    (γ : Level → Level → Level)
    : UUω
  where

  constructor make-Large-Wild-1-Precategory

  field
    large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory :
      Large-Wild-⟨0,1⟩-Precategory α β γ

  obj-Large-Wild-1-Precategory : (l : Level) → UU (α l)
  obj-Large-Wild-1-Precategory =
    obj-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)

  hom-Large-Wild-1-Precategory :
    {l1 l2 : Level} →
    obj-Large-Wild-1-Precategory l1 →
    obj-Large-Wild-1-Precategory l2 →
    UU (β l1 l2)
  hom-Large-Wild-1-Precategory =
    hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)

  comp-hom-Large-Wild-1-Precategory :
    {l1 l2 l3 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2}
    {Z : obj-Large-Wild-1-Precategory l3} →
    hom-Large-Wild-1-Precategory Y Z →
    hom-Large-Wild-1-Precategory X Y →
    hom-Large-Wild-1-Precategory X Z
  comp-hom-Large-Wild-1-Precategory =
    comp-hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)

  id-hom-Large-Wild-1-Precategory :
    {l1 : Level}
    {X : obj-Large-Wild-1-Precategory l1} →
    hom-Large-Wild-1-Precategory X X
  id-hom-Large-Wild-1-Precategory =
    id-hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)

  relation-hom-Large-Wild-1-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2} →
    Relation
      ( γ l1 l2)
      ( hom-Large-Wild-1-Precategory X Y)
  relation-hom-Large-Wild-1-Precategory =
    relation-hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)

  is-wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Wild-1-Precategory l1}
      {Y : obj-Large-Wild-1-Precategory l2} →
      is-wild-0-pregroupoid
        ( relation-hom-Large-Wild-1-Precategory {X = X} {Y})
  is-wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory =
    is-wild-0-pregroupoid-relation-hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)

  wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2} →
    Wild-0-Pregroupoid-Relation (γ l1 l2) (hom-Large-Wild-1-Precategory X Y)
  wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory =
    wild-0-pregroupoid-relation-hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)

  refl-relation-hom-Large-Wild-1-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2} →
    {f : hom-Large-Wild-1-Precategory X Y} →
    relation-hom-Large-Wild-1-Precategory f f
  refl-relation-hom-Large-Wild-1-Precategory =
    refl-Wild-0-Pregroupoid-Relation
      ( wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory)

  inv-relation-hom-Large-Wild-1-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2} →
    {f g : hom-Large-Wild-1-Precategory X Y} →
    relation-hom-Large-Wild-1-Precategory f g →
    relation-hom-Large-Wild-1-Precategory g f
  inv-relation-hom-Large-Wild-1-Precategory =
    inv-Wild-0-Pregroupoid-Relation
      ( wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory)

  comp-relation-hom-Large-Wild-1-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2} →
    {f g h : hom-Large-Wild-1-Precategory X Y} →
    relation-hom-Large-Wild-1-Precategory g h →
    relation-hom-Large-Wild-1-Precategory f g →
    relation-hom-Large-Wild-1-Precategory f h
  comp-relation-hom-Large-Wild-1-Precategory =
    comp-Wild-0-Pregroupoid-Relation
      ( wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory)

  field
    left-unit-comp-hom-Large-Wild-1-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Wild-1-Precategory l1}
      {Y : obj-Large-Wild-1-Precategory l2} →
      (f : hom-Large-Wild-1-Precategory X Y) →
      relation-hom-Large-Wild-1-Precategory
        ( comp-hom-Large-Wild-1-Precategory
          ( id-hom-Large-Wild-1-Precategory)
          ( f))
        ( f)

    right-unit-comp-hom-Large-Wild-1-Precategory :
      {l1 l2 : Level}
      {X :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l1)}
      {Y :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l2)} →
      (f :
        hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( X)
          ( Y)) →
      relation-hom-Large-Wild-⟨0,1⟩-Precategory
        ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
        ( comp-hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( f)
          ( id-hom-Large-Wild-⟨0,1⟩-Precategory
            ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)))
        ( f)
```

We assume the associator using the strict symmetrization of the relation, so
that the opposite large wild 1-precategory construction is a strict involution.

```agda
    symmetrization-associative-comp-hom-Large-Wild-1-Precategory :
      {l1 l2 l3 l4 : Level}
      {X :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l1)}
      {Y :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l2)}
      {Z :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l3)}
      {W :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l4)} →
      (h :
        hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( Z)
          ( W))
      (g :
        hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( Y)
          ( Z))
      (f :
        hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( X)
          ( Y)) →
      strict-symmetrization-Relation
        ( relation-hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory))
        ( comp-hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( comp-hom-Large-Wild-⟨0,1⟩-Precategory
            ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
            ( h)
            ( g))
          ( f))
        ( comp-hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( h)
          ( comp-hom-Large-Wild-⟨0,1⟩-Precategory
            ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
            ( g)
            ( f)))

  associative-comp-hom-Large-Wild-1-Precategory :
    {l1 l2 l3 l4 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2}
    {Z : obj-Large-Wild-1-Precategory l3}
    {W : obj-Large-Wild-1-Precategory l4}
    (h : hom-Large-Wild-1-Precategory Z W)
    (g : hom-Large-Wild-1-Precategory Y Z)
    (f : hom-Large-Wild-1-Precategory X Y) →
    relation-hom-Large-Wild-1-Precategory
      ( comp-hom-Large-Wild-1-Precategory
        ( comp-hom-Large-Wild-1-Precategory h g)
        ( f))
      ( comp-hom-Large-Wild-1-Precategory
        ( h)
        ( comp-hom-Large-Wild-1-Precategory g f))
  associative-comp-hom-Large-Wild-1-Precategory h g f =
    counit-strict-symmetrization-Wild-0-Pregroupoid-Relation
      ( relation-hom-Large-Wild-1-Precategory ,
        is-wild-0-pregroupoid-relation-hom-Large-Wild-1-Precategory)
      ( symmetrization-associative-comp-hom-Large-Wild-1-Precategory h g f)

open Large-Wild-1-Precategory public
```
