# Homotopies of natural transformations in large precategories

```agda
module category-theory.homotopies-natural-transformations-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-large-precategories

open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Two
[natural transformations](category-theory.natural-transformations-large-precategories.md)
`α β : F ⇒ G` are **homotopic** if for every object `x` there is an
[identification](foundation-core.identity-types.md) `α x ＝ β x`.

In `UUω` the usual identity type is not available. If it were, we would be able
to characterize the identity type of natural transformations from `F` to `G` as
the type of homotopies of natural transformations.

## Definitions

### Homotopies of natural transformations

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC} {D : Large-Precategory αD βD}
  {F : functor-Large-Precategory C D γF}
  {G : functor-Large-Precategory C D γG}
  where

  htpy-natural-transformation-Large-Precategory :
    (α β : natural-transformation-Large-Precategory F G) → UUω
  htpy-natural-transformation-Large-Precategory α β =
    { l : Level} (X : obj-Large-Precategory C l) →
    ( hom-family-natural-transformation-Large-Precategory α X) ＝
    ( hom-family-natural-transformation-Large-Precategory β X)
```

### The reflexivity homotopy

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precategory αC βC} {D : Large-Precategory αD βD}
  {F : functor-Large-Precategory C D γF}
  {G : functor-Large-Precategory C D γG}
  where

  refl-htpy-natural-transformation-Large-Precategory :
    (α : natural-transformation-Large-Precategory F G) →
    htpy-natural-transformation-Large-Precategory α α
  refl-htpy-natural-transformation-Large-Precategory α = refl-htpy
```

### Concatenation of homotopies

A homotopy from `α` to `β` can be concatenated with a homotopy from `β` to `γ`
to form a homotopy from `α` to `γ`. The concatenation is associative.

```agda
  concat-htpy-natural-transformation-Large-Precategory :
    (α β γ : natural-transformation-Large-Precategory F G) →
    htpy-natural-transformation-Large-Precategory α β →
    htpy-natural-transformation-Large-Precategory β γ →
    htpy-natural-transformation-Large-Precategory α γ
  concat-htpy-natural-transformation-Large-Precategory α β γ H K = H ∙h K

  associative-concat-htpy-natural-transformation-Large-Precategory :
    (α β γ δ : natural-transformation-Large-Precategory F G)
    (H : htpy-natural-transformation-Large-Precategory α β)
    (K : htpy-natural-transformation-Large-Precategory β γ)
    (L : htpy-natural-transformation-Large-Precategory γ δ) →
    {l : Level} (X : obj-Large-Precategory C l) →
    ( concat-htpy-natural-transformation-Large-Precategory α γ δ
      ( concat-htpy-natural-transformation-Large-Precategory α β γ H K)
      ( L)
      ( X)) ＝
    ( concat-htpy-natural-transformation-Large-Precategory α β δ
      ( H)
      ( concat-htpy-natural-transformation-Large-Precategory β γ δ K L)
      ( X))
  associative-concat-htpy-natural-transformation-Large-Precategory
    α β γ δ H K L =
    assoc-htpy H K L
```
