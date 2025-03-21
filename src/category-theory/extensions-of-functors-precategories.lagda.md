# Extensions of functors between precategories

```agda
module category-theory.extensions-of-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a functor between precategories" Agda=is-extension-functor-Precategory}}
[functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) along another functor
`p : C → C'` is a functor `G : C' → D` such that `g ∘ p ＝ G`.

```text
  C
  |  \
  p    F
  |      \
  ∨        ∨
  C' - G -> D
```

## Definition

### Extensions of dependent functions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C')
  where

  is-extension-functor-Precategory :
    functor-Precategory C D → functor-Precategory C' D → UU (l1 ⊔ l2 ⊔ l5 ⊔ l6)
  is-extension-functor-Precategory F G =
    comp-functor-Precategory C C' D G p ＝ F

  extension-functor-Precategory :
    functor-Precategory C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  extension-functor-Precategory F =
    Σ (functor-Precategory C' D) (is-extension-functor-Precategory F)
```
