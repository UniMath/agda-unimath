# Large wild (0,1)-precategories

```agda
module wild-category-theory.large-wild-0-1-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import wild-category-theory.wild-0-pregroupoids
```

</details>

## Idea

A {{#concept "large wild (0,1)-precategory" }} is...

## Definitions

### Large wild (0,1)-precategories

```agda
record
  Large-Wild-⟨0,1⟩-Precategory
  (α : Level → Level) (β γ : Level → Level → Level)
  : UUω
  where

  constructor make-Large-Wild-⟨0,1⟩-Precategory

  field
    obj-Large-Wild-⟨0,1⟩-Precategory :
      (l : Level) → UU (α l)

    hom-Large-Wild-⟨0,1⟩-Precategory :
      {l1 l2 : Level} →
      obj-Large-Wild-⟨0,1⟩-Precategory l1 →
      obj-Large-Wild-⟨0,1⟩-Precategory l2 →
      UU (β l1 l2)

    comp-hom-Large-Wild-⟨0,1⟩-Precategory :
      {l1 l2 l3 : Level}
      {X : obj-Large-Wild-⟨0,1⟩-Precategory l1}
      {Y : obj-Large-Wild-⟨0,1⟩-Precategory l2}
      {Z : obj-Large-Wild-⟨0,1⟩-Precategory l3} →
      hom-Large-Wild-⟨0,1⟩-Precategory Y Z →
      hom-Large-Wild-⟨0,1⟩-Precategory X Y →
      hom-Large-Wild-⟨0,1⟩-Precategory X Z

    id-hom-Large-Wild-⟨0,1⟩-Precategory :
      {l1 : Level}
      {X : obj-Large-Wild-⟨0,1⟩-Precategory l1} →
      hom-Large-Wild-⟨0,1⟩-Precategory X X

    relation-hom-Large-Wild-⟨0,1⟩-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Wild-⟨0,1⟩-Precategory l1}
      {Y : obj-Large-Wild-⟨0,1⟩-Precategory l2} →
      Relation
        ( γ l1 l2)
        ( hom-Large-Wild-⟨0,1⟩-Precategory X Y)

    is-Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory :
      {l1 l2 : Level}
      {X : obj-Large-Wild-⟨0,1⟩-Precategory l1}
      {Y : obj-Large-Wild-⟨0,1⟩-Precategory l2} →
      is-wild-0-pregroupoid
        ( relation-hom-Large-Wild-⟨0,1⟩-Precategory {X = X} {Y})
```

We also record a range of common projections.

```agda
  Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-⟨0,1⟩-Precategory l1}
    {Y : obj-Large-Wild-⟨0,1⟩-Precategory l2} →
    Wild-0-Pregroupoid (γ l1 l2) (hom-Large-Wild-⟨0,1⟩-Precategory X Y)
  pr1 Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory =
    relation-hom-Large-Wild-⟨0,1⟩-Precategory
  pr2 Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory =
    is-Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory

  refl-relation-hom-Large-Wild-⟨0,1⟩-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-⟨0,1⟩-Precategory l1}
    {Y : obj-Large-Wild-⟨0,1⟩-Precategory l2}
    {f : hom-Large-Wild-⟨0,1⟩-Precategory X Y} →
    relation-hom-Large-Wild-⟨0,1⟩-Precategory f f
  refl-relation-hom-Large-Wild-⟨0,1⟩-Precategory =
    refl-Wild-0-Pregroupoid
      ( Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory)

  inv-relation-hom-Large-Wild-⟨0,1⟩-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-⟨0,1⟩-Precategory l1}
    {Y : obj-Large-Wild-⟨0,1⟩-Precategory l2}
    {f g : hom-Large-Wild-⟨0,1⟩-Precategory X Y} →
    relation-hom-Large-Wild-⟨0,1⟩-Precategory f g →
    relation-hom-Large-Wild-⟨0,1⟩-Precategory g f
  inv-relation-hom-Large-Wild-⟨0,1⟩-Precategory =
    inv-Wild-0-Pregroupoid
      ( Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory)

  comp-relation-hom-Large-Wild-⟨0,1⟩-Precategory :
    {l1 l2 : Level}
    {X : obj-Large-Wild-⟨0,1⟩-Precategory l1}
    {Y : obj-Large-Wild-⟨0,1⟩-Precategory l2}
    {f g h : hom-Large-Wild-⟨0,1⟩-Precategory X Y} →
    relation-hom-Large-Wild-⟨0,1⟩-Precategory g h →
    relation-hom-Large-Wild-⟨0,1⟩-Precategory f g →
    relation-hom-Large-Wild-⟨0,1⟩-Precategory f h
  comp-relation-hom-Large-Wild-⟨0,1⟩-Precategory =
    comp-Wild-0-Pregroupoid
      ( Wild-0-Pregroupoid-hom-Large-Wild-⟨0,1⟩-Precategory)

open Large-Wild-⟨0,1⟩-Precategory public
```
