# Large wild 1-precategories

```agda
module wild-category-theory.large-wild-1-precategories where
```

<details><summary>Imports</summary>

```agda
open import wild-category-theory.large-wild-⟨0,1⟩-precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.large-binary-relations
open import foundation.binary-relations
open import foundation.strict-symmetrization-binary-relations
open import foundation.contratransitive-binary-relations
open import foundation.universe-levels
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
      Large-Wild-⟨0,1⟩-Precategory α β

    relation-hom-Large-Wild-1-Precategory :
      {l1 l2 : Level}
      {X :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l1)}
      {Y :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l2)} →
      Relation
        ( γ l1 l2)
        ( hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( X)
          ( Y))

    is-right-contratransitive-relation-hom-Large-Wild-1-Precategory :
      {l1 l2 : Level}
      {X :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l1)}
      {Y :
        obj-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( l2)} →
      is-right-contratransitive (relation-hom-Large-Wild-1-Precategory {X = X} {Y})

    left-unit-comp-hom-Large-Wild-1-Precategory :
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
      relation-hom-Large-Wild-1-Precategory
        ( comp-hom-Large-Wild-⟨0,1⟩-Precategory
          ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory)
          ( id-hom-Large-Wild-⟨0,1⟩-Precategory
            ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory))
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
      relation-hom-Large-Wild-1-Precategory
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
        ( relation-hom-Large-Wild-1-Precategory)
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

open Large-Wild-1-Precategory public
```

We record all the standard projections for the type of large wild
1-precategories.

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {γ : Level → Level → Level}
  (𝒞 : Large-Wild-1-Precategory α β γ)
  where

  obj-Large-Wild-1-Precategory : (l : Level) → UU (α l)
  obj-Large-Wild-1-Precategory =
    obj-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory 𝒞)

  hom-Large-Wild-1-Precategory :
    {l1 l2 : Level} →
    obj-Large-Wild-1-Precategory l1 →
    obj-Large-Wild-1-Precategory l2 →
    UU (β l1 l2)
  hom-Large-Wild-1-Precategory =
    hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory 𝒞)

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
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory 𝒞)

  id-hom-Large-Wild-1-Precategory :
    {l1 : Level}
    {X : obj-Large-Wild-1-Precategory l1} →
    hom-Large-Wild-1-Precategory X X
  id-hom-Large-Wild-1-Precategory =
    id-hom-Large-Wild-⟨0,1⟩-Precategory
      ( large-wild-⟨0,1⟩-precategory-Large-Wild-1-Precategory 𝒞)

  associative-comp-hom-Large-Wild-1-Precategory :
    {l1 l2 l3 l4 : Level}
    {X : obj-Large-Wild-1-Precategory l1}
    {Y : obj-Large-Wild-1-Precategory l2}
    {Z : obj-Large-Wild-1-Precategory l3}
    {W : obj-Large-Wild-1-Precategory l4}
    (h : hom-Large-Wild-1-Precategory Z W)
    (g : hom-Large-Wild-1-Precategory Y Z)
    (f : hom-Large-Wild-1-Precategory X Y) →
    relation-hom-Large-Wild-1-Precategory 𝒞
      ( comp-hom-Large-Wild-1-Precategory
        ( comp-hom-Large-Wild-1-Precategory h g)
        ( f))
      ( comp-hom-Large-Wild-1-Precategory
        ( h)
        ( comp-hom-Large-Wild-1-Precategory g f))
  associative-comp-hom-Large-Wild-1-Precategory h g f =
    counit-strict-symmetrization-Relation
      ( relation-hom-Large-Wild-1-Precategory 𝒞)
      ( is-right-contratransitive-relation-hom-Large-Wild-1-Precategory 𝒞)
      ( symmetrization-associative-comp-hom-Large-Wild-1-Precategory 𝒞 h g f)
```
