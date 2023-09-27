# Large subprecategories

```agda
module category-theory.large-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **large subprecategory** of a
[large precategory](category-theory.large-precategories.md) `C` consists of a
family of subtypes `P₀`

```text
  P₀ : (l : Level) → subtype _ (obj C l)
```

of the objects of `C` indexed by universe levels, and a family of subtypes `P₁`

```text
  P₁ : {l1 l2 : Level} (X : obj C l1) (Y : obj C l2) →
       P₀ X → P₀ Y → subtype _ (hom X Y)
```

of the morphisms of `C`, such that `P₁` contains all identity morphisms of
objects in `P₀` and is closed under composition.

## Definition

### Large subprecategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (γ : Level → Level) (δ : Level → Level → Level)
  (C : Large-Precategory α β)
  where

  record
    Large-Subprecategory : UUω
    where
    field
      subtype-obj-Large-Subprecategory :
        (l : Level) → subtype (γ l) (obj-Large-Precategory C l)
      subtype-hom-Large-Subprecategory :
        {l1 l2 : Level}
        (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2) →
        is-in-subtype (subtype-obj-Large-Subprecategory l1) X →
        is-in-subtype (subtype-obj-Large-Subprecategory l2) Y →
        subtype (β l1 l2) (hom-Large-Precategory C X Y)
      contains-id-Large-Subprecategory :
        {l1 : Level} (X : obj-Large-Precategory C l1) →
        (H : is-in-subtype (subtype-obj-Large-Subprecategory l1) X) →
        is-in-subtype
          ( subtype-hom-Large-Subprecategory X X H H)
          ( id-hom-Large-Precategory C)
      is-closed-under-composition-Large-Subprecategory :
        {l1 l2 l3 : Level}
        (X : obj-Large-Precategory C l1)
        (Y : obj-Large-Precategory C l2)
        (Z : obj-Large-Precategory C l3)
        (g : hom-Large-Precategory C Y Z)
        (f : hom-Large-Precategory C X Y) →
        (K : is-in-subtype (subtype-obj-Large-Subprecategory l1) X) →
        (L : is-in-subtype (subtype-obj-Large-Subprecategory l2) Y) →
        (M : is-in-subtype (subtype-obj-Large-Subprecategory l3) Z) →
        is-in-subtype (subtype-hom-Large-Subprecategory Y Z L M) g →
        is-in-subtype (subtype-hom-Large-Subprecategory X Y K L) f →
        is-in-subtype
          ( subtype-hom-Large-Subprecategory X Z K M)
          ( comp-hom-Large-Precategory C g f)

  open Large-Subprecategory public

module _
  {α : Level → Level} {β : Level → Level → Level}
  {γ : Level → Level} {δ : Level → Level → Level}
  (C : Large-Precategory α β)
  (P : Large-Subprecategory γ δ C)
  where

  is-in-subtype-obj-Large-Subprecategory :
    {l : Level} → obj-Large-Precategory C l → UU (γ l)
  is-in-subtype-obj-Large-Subprecategory =
    is-in-subtype (subtype-obj-Large-Subprecategory P _)
```
