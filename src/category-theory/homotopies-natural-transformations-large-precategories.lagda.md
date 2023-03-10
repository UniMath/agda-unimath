# Homotopies of natural transformations in large precategories

```agda
module category-theory.homotopies-natural-transformations-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import Agda.Primitive using (Setω)

open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-transformations-large-precategories

open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Two natural transformations `α β : F ⇒ G` are homotopic if for every object `x` there is an identity `Id (α x) (β x)`.

In `Setω` the identity type is not available. If it were, we would be able to characterize the identity type of natural transformations from `F` to `G` as the type of homotopies of natural transformations.

## Definition

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  {F : functor-Large-Precat C D γF} {G : functor-Large-Precat C D γG}
  where

  htpy-natural-transformation-Large-Precat :
    (α β : natural-transformation-Large-Precat F G) → Setω
  htpy-natural-transformation-Large-Precat α β =
    {l : Level} (X : obj-Large-Precat C l) →
    ( obj-natural-transformation-Large-Precat α X) ＝
    ( obj-natural-transformation-Large-Precat β X)
```

## Examples

### Reflexivity homotopy

Any natural transformation is homotopic to itself.

```agda
module _
  {αC αD γF γG : Level → Level} {βC βD : Level → Level → Level}
  {C : Large-Precat αC βC} {D : Large-Precat αD βD}
  {F : functor-Large-Precat C D γF} {G : functor-Large-Precat C D γG}
  where

  refl-htpy-natural-transformation-Large-Precat :
    (α : natural-transformation-Large-Precat F G) →
    htpy-natural-transformation-Large-Precat α α
  refl-htpy-natural-transformation-Large-Precat α = refl-htpy
```

### Concatenation of homotopies

A homotopy from `α` to `β` can be concatenated with a homotopy from `β` to `γ` to form a homotopy from `α` to `γ`. The concatenation is associative.

```agda
  concat-htpy-natural-transformation-Large-Precat :
    (α β γ : natural-transformation-Large-Precat F G) →
    htpy-natural-transformation-Large-Precat α β →
    htpy-natural-transformation-Large-Precat β γ →
    htpy-natural-transformation-Large-Precat α γ
  concat-htpy-natural-transformation-Large-Precat α β γ H K X =
    H X ∙ K X

  associative-concat-htpy-natural-transformation-Large-Precat :
    (α β γ δ : natural-transformation-Large-Precat F G)
    (H : htpy-natural-transformation-Large-Precat α β)
    (K : htpy-natural-transformation-Large-Precat β γ)
    (L : htpy-natural-transformation-Large-Precat γ δ) →
    {l : Level} (X : obj-Large-Precat C l) →
    ( concat-htpy-natural-transformation-Large-Precat α γ δ
      ( concat-htpy-natural-transformation-Large-Precat α β γ H K)
      ( L)
      ( X)) ＝
    ( concat-htpy-natural-transformation-Large-Precat α β δ
      ( H)
      ( concat-htpy-natural-transformation-Large-Precat β γ δ K L)
      ( X))
  associative-concat-htpy-natural-transformation-Large-Precat α β γ δ H K L X =
    assoc (H X) (K X) (L X)
```
