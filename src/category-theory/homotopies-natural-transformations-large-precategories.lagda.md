# Homotopies of natural transformations in large precategories

```agda
module category-theory.homotopies-natural-transformations-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-functors-large-precategories

open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Two
[natural transformations](category-theory.natural-transformations-functors-large-precategories.md)
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
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  {F : functor-Large-Precategory γF C D}
  {G : functor-Large-Precategory γG C D}
  where

  htpy-natural-transformation-Large-Precategory :
    (σ τ : natural-transformation-Large-Precategory C D F G) → UUω
  htpy-natural-transformation-Large-Precategory σ τ =
    { l : Level} (X : obj-Large-Precategory C l) →
    ( hom-natural-transformation-Large-Precategory σ X) ＝
    ( hom-natural-transformation-Large-Precategory τ X)
```

### The reflexivity homotopy

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  {F : functor-Large-Precategory γF C D}
  {G : functor-Large-Precategory γG C D}
  where

  refl-htpy-natural-transformation-Large-Precategory :
    (α : natural-transformation-Large-Precategory C D F G) →
    htpy-natural-transformation-Large-Precategory C D α α
  refl-htpy-natural-transformation-Large-Precategory α = refl-htpy
```

### Concatenation of homotopies

A homotopy from `α` to `β` can be concatenated with a homotopy from `β` to `γ`
to form a homotopy from `α` to `γ`. The concatenation is associative.

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  {F : functor-Large-Precategory γF C D}
  {G : functor-Large-Precategory γG C D}
  where

  concat-htpy-natural-transformation-Large-Precategory :
    (σ τ υ : natural-transformation-Large-Precategory C D F G) →
    htpy-natural-transformation-Large-Precategory C D σ τ →
    htpy-natural-transformation-Large-Precategory C D τ υ →
    htpy-natural-transformation-Large-Precategory C D σ υ
  concat-htpy-natural-transformation-Large-Precategory σ τ υ H K = H ∙h K

  associative-concat-htpy-natural-transformation-Large-Precategory :
    (σ τ υ ϕ : natural-transformation-Large-Precategory C D F G)
    (H : htpy-natural-transformation-Large-Precategory C D σ τ)
    (K : htpy-natural-transformation-Large-Precategory C D τ υ)
    (L : htpy-natural-transformation-Large-Precategory C D υ ϕ) →
    {l : Level} (X : obj-Large-Precategory C l) →
    ( concat-htpy-natural-transformation-Large-Precategory σ υ ϕ
      ( concat-htpy-natural-transformation-Large-Precategory σ τ υ H K)
      ( L)
      ( X)) ＝
    ( concat-htpy-natural-transformation-Large-Precategory σ τ ϕ
      ( H)
      ( concat-htpy-natural-transformation-Large-Precategory τ υ ϕ K L)
      ( X))
  associative-concat-htpy-natural-transformation-Large-Precategory
    σ τ υ ϕ H K L =
    assoc-htpy H K L
```
