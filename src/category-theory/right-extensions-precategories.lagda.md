# Right extensions in precategories

```agda
module category-theory.right-extensions-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.action-on-equivalences-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.multivariable-homotopies
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.functoriality-dependent-function-types
```

</details>

## Idea

A
{{#concept "right extension" Disambiguation="of a functor between precategories" Agda=right-extension-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) along another functor
`p : C → C'` is a functor `G : C' → D` together with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
`φ : G ∘ p → F`.

```text
    C
    |  \
  p |    \ F
    |      \
    ∨        ∨
    C' -----> D
         G
```

We note that this is not a standard definition, but is inspired by the notion of
a [right Kan extension](category-theory.right-kan-extensions-precategories.md).

## Definition

### Right extensions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  where

  right-extension-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  right-extension-Precategory =
    Σ ( functor-Precategory C' D)
      ( λ G →
        natural-transformation-Precategory C D
          ( comp-functor-Precategory C C' D G p)
          ( F))

  module _
    (R : right-extension-Precategory)
    where

    extension-right-extension-Precategory : functor-Precategory C' D
    extension-right-extension-Precategory = pr1 R

    natural-transformation-right-extension-Precategory :
      natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
    natural-transformation-right-extension-Precategory = pr2 R

    hom-family-right-extension-Precategory :
      hom-family-functor-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
    hom-family-right-extension-Precategory =
      hom-family-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
        ( natural-transformation-right-extension-Precategory)

    naturality-right-extension-Precategory :
      is-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
        ( hom-family-right-extension-Precategory)
    naturality-right-extension-Precategory =
      naturality-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
        ( natural-transformation-right-extension-Precategory)
```

### Precomposing right extensions

```agda
    right-extension-map-Precategory :
      ( G : functor-Precategory C' D) →
      ( natural-transformation-Precategory C' D
        G extension-right-extension-Precategory) →
      ( natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D G p) F)
    right-extension-map-Precategory G φ =
      comp-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D G p)
        ( comp-functor-Precategory C C' D
          extension-right-extension-Precategory p)
        ( F)
        ( natural-transformation-right-extension-Precategory)
        ( right-whisker-natural-transformation-Precategory C' D C
          ( G)
          ( extension-right-extension-Precategory)
          ( φ)
          ( p))
```

## Properties

### Characterization of equality between right extensions of functors between precategories

```agda
  coherence-htpy-right-extension-Precategory :
    (R S : right-extension-Precategory)
    (e :
      (extension-right-extension-Precategory R) ＝
      (extension-right-extension-Precategory S)) →
    UU (l1 ⊔ l6)
  coherence-htpy-right-extension-Precategory R S e =
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-family-right-extension-Precategory S x)
      ( hom-family-natural-transformation-Precategory C' D (pr1 R) (pr1 S)
        ( natural-transformation-eq-Precategory C' D
          ( extension-right-extension-Precategory R)
          ( extension-right-extension-Precategory S)
          ( e))
        ( obj-functor-Precategory C C' p x)) ＝
    hom-family-right-extension-Precategory R x

  htpy-right-extension-Precategory :
    (R S : right-extension-Precategory) →
    UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  htpy-right-extension-Precategory R S =
    Σ ( extension-right-extension-Precategory R ＝
        extension-right-extension-Precategory S)
      ( coherence-htpy-right-extension-Precategory R S)

  is-torsorial-htpy-right-extension-Precategory :
    (R : right-extension-Precategory) →
    is-torsorial (htpy-right-extension-Precategory R)
  is-torsorial-htpy-right-extension-Precategory R =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (extension-right-extension-Precategory R))
      ( pair (extension-right-extension-Precategory R) refl)
      ( is-contr-equiv
        ( Σ
          ( natural-transformation-Precategory C D
            ( comp-functor-Precategory C C' D
              ( extension-right-extension-Precategory R) p)
            ( F))
          ( λ τ → τ ＝ natural-transformation-right-extension-Precategory R))
        ( equiv-tot
          ( λ τ →
            inv-equiv
              ( extensionality-natural-transformation-Precategory C D
                ( comp-functor-Precategory C C' D
                  ( extension-right-extension-Precategory R) p)
                ( F) _ _) ∘e
            equiv-Π-equiv-family
              ( λ x →
                equiv-inv-concat
                  ( right-unit-law-comp-hom-Precategory D _)
                  ( hom-family-right-extension-Precategory R x))))
        ( is-torsorial-Id'
          ( natural-transformation-right-extension-Precategory R)))

  refl-htpy-right-extension-Precategory :
    (R : right-extension-Precategory) →
    htpy-right-extension-Precategory R R
  pr1 (refl-htpy-right-extension-Precategory R) = refl
  pr2 (refl-htpy-right-extension-Precategory R) x =
    right-unit-law-comp-hom-Precategory D _

  htpy-eq-right-extension-Precategory :
    (R S : right-extension-Precategory) →
    R ＝ S →
    htpy-right-extension-Precategory R S
  htpy-eq-right-extension-Precategory R .R refl =
    refl-htpy-right-extension-Precategory R

  is-equiv-htpy-eq-right-extension-Precategory :
    (R S : right-extension-Precategory) →
    is-equiv (htpy-eq-right-extension-Precategory R S)
  is-equiv-htpy-eq-right-extension-Precategory R =
    fundamental-theorem-id
      ( is-torsorial-htpy-right-extension-Precategory R)
      ( htpy-eq-right-extension-Precategory R)

  equiv-htpy-eq-right-extension-Precategory :
    (R S : right-extension-Precategory) →
    (R ＝ S) ≃ htpy-right-extension-Precategory R S
  pr1 (equiv-htpy-eq-right-extension-Precategory R S) =
    htpy-eq-right-extension-Precategory R S
  pr2 (equiv-htpy-eq-right-extension-Precategory R S) =
    is-equiv-htpy-eq-right-extension-Precategory R S

  eq-htpy-right-extension-Precategory :
    (R S : right-extension-Precategory) →
    htpy-right-extension-Precategory R S →
    R ＝ S
  eq-htpy-right-extension-Precategory R S =
    map-inv-equiv (equiv-htpy-eq-right-extension-Precategory R S)
```

### Self-extensions

In the case of extending a functor along itself, we have distinguished right
extensions: the identity map gives a right extension (with the identity natural
transformation) and we can iterate any right extension `R` to get a right
extension `R²`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  id-right-extension-Precategory : right-extension-Precategory C D D F F
  pr1 id-right-extension-Precategory = id-functor-Precategory D
  pr2 id-right-extension-Precategory =
    id-natural-transformation-Precategory C D F

  extension-square-right-extension-Precategory :
    (R : right-extension-Precategory C D D F F) →
    functor-Precategory D D
  extension-square-right-extension-Precategory R =
    comp-functor-Precategory D D D
      ( extension-right-extension-Precategory C D D F F R)
      ( extension-right-extension-Precategory C D D F F R)

  natural-transformation-square-right-extension-Precategory :
    (R : right-extension-Precategory C D D F F) →
    natural-transformation-Precategory C D
      ( comp-functor-Precategory C D D
        ( extension-square-right-extension-Precategory R)
        ( F))
      ( F)
  natural-transformation-square-right-extension-Precategory R =
    comp-natural-transformation-Precategory C D
      ( comp-functor-Precategory C D D
        ( comp-functor-Precategory D D D
          ( extension-right-extension-Precategory C D D F F R)
          ( extension-right-extension-Precategory C D D F F R))
        ( F))
      ( comp-functor-Precategory C D D
        ( extension-right-extension-Precategory C D D F F R)
        ( F))
      ( F)
      ( natural-transformation-right-extension-Precategory C D D F F R)
      ( left-whisker-natural-transformation-Precategory C D D
        ( comp-functor-Precategory C D D
          ( extension-right-extension-Precategory C D D F F R)
          ( F))
        ( F)
        ( extension-right-extension-Precategory C D D F F R)
        ( natural-transformation-right-extension-Precategory C D D F F R))

  square-right-extension-Precategory :
    (R : right-extension-Precategory C D D F F) →
    right-extension-Precategory C D D F F
  square-right-extension-Precategory R =
    ( extension-square-right-extension-Precategory R ,
      natural-transformation-square-right-extension-Precategory R)
```

## See also

- [Left extensions](category-theory.left-extensions-precategories.md) for the
  dual concept.
