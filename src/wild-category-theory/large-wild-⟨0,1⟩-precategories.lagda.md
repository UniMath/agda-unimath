# Large wild (0,1)-precategories

```agda
module wild-category-theory.large-wild-⟨0,1⟩-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.nonunital-precategories
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large wild (0,1)-precategory" }} is...

## Definitions

### Large wild 0 precategories

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
