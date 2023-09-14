# Terminal object of a precategory

```agda
module category-theory.terminal-objects-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The terminal object of a precategory (if it exists) is an object with the
universal property that there is a unique morphism into it from any object.

## Definition

```agda
terminal-object-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
terminal-object-Precategory C =
  Σ (obj-Precategory C) λ t →
    (x : obj-Precategory C) → is-contr (type-hom-Precategory C x t)

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (t : terminal-object-Precategory C)
  where

  object-terminal-object-Precategory : obj-Precategory C
  object-terminal-object-Precategory = pr1 t

  morphism-terminal-object-Precategory :
    (x : obj-Precategory C) →
    type-hom-Precategory C x object-terminal-object-Precategory
  morphism-terminal-object-Precategory x = pr1 (pr2 t x)

  is-unique-morphism-terminal-object-Precategory :
    (x : obj-Precategory C) →
    (f : type-hom-Precategory C x object-terminal-object-Precategory) →
    morphism-terminal-object-Precategory x ＝ f
  is-unique-morphism-terminal-object-Precategory x = pr2 (pr2 t x)
```
