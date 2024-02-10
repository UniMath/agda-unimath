# Large wild (0,1)-precategories

```agda
module wild-category-theory.large-wild-⟨0,1⟩-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large wild (0,1)-precategory" }} is...

## Definitions

### Large wild 0-precategories

```agda
record
  Large-Wild-⟨0,1⟩-Precategory (α : Level → Level) (β : Level → Level → Level)
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

open Large-Wild-⟨0,1⟩-Precategory public
```
