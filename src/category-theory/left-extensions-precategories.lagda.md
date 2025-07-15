# Left extensions in precategories

```agda
module category-theory.left-extensions-precategories where
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
{{#concept "left extension" Disambiguation="of a functor between precategories" Agda=left-extension-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) along another functor
`p : C → C'` is a functor `G : C' → D` together with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
`φ : F → G ∘ p`.

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
a [left Kan extension](category-theory.left-kan-extensions-precategories.md).

## Definition

### Left extensions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  where

  left-extension-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  left-extension-Precategory =
    Σ ( functor-Precategory C' D)
      ( λ G →
        natural-transformation-Precategory C D
          ( F)
          ( comp-functor-Precategory C C' D G p))

  module _
    (L : left-extension-Precategory)
    where

    extension-left-extension-Precategory : functor-Precategory C' D
    extension-left-extension-Precategory = pr1 L

    natural-transformation-left-extension-Precategory :
      natural-transformation-Precategory C D
        ( F)
        ( comp-functor-Precategory C C' D
          ( extension-left-extension-Precategory)
          ( p))
    natural-transformation-left-extension-Precategory = pr2 L

    hom-family-left-extension-Precategory :
      hom-family-functor-Precategory C D
        ( F)
        ( comp-functor-Precategory C C' D
          ( extension-left-extension-Precategory)
          ( p))
    hom-family-left-extension-Precategory =
      hom-family-natural-transformation-Precategory C D
        ( F)
        ( comp-functor-Precategory C C' D
          ( extension-left-extension-Precategory)
          ( p))
        ( natural-transformation-left-extension-Precategory)

    naturality-left-extension-Precategory :
      is-natural-transformation-Precategory C D
        ( F)
        ( comp-functor-Precategory C C' D
          ( extension-left-extension-Precategory)
          ( p))
        ( hom-family-left-extension-Precategory)
    naturality-left-extension-Precategory =
      naturality-natural-transformation-Precategory C D
        ( F)
        ( comp-functor-Precategory C C' D
          ( extension-left-extension-Precategory)
          ( p))
        ( natural-transformation-left-extension-Precategory)
```

### Postcomposing left extensions

```agda
    left-extension-map-Precategory :
      ( G : functor-Precategory C' D) →
      ( natural-transformation-Precategory C' D
        extension-left-extension-Precategory G) →
      ( natural-transformation-Precategory C D
        F ( comp-functor-Precategory C C' D G p))
    left-extension-map-Precategory G φ =
      comp-natural-transformation-Precategory C D
        ( F)
        ( comp-functor-Precategory C C' D
          extension-left-extension-Precategory p)
        ( comp-functor-Precategory C C' D G p)
        ( right-whisker-natural-transformation-Precategory C' D C
          ( extension-left-extension-Precategory)
          ( G)
          ( φ)
          ( p))
        ( natural-transformation-left-extension-Precategory)
```

## Properties

### Characterization of equality between left extensions of functors between precategories

```agda
  coherence-htpy-left-extension-Precategory :
    (R S : left-extension-Precategory)
    (e :
      (extension-left-extension-Precategory R) ＝
      (extension-left-extension-Precategory S)) →
    UU (l1 ⊔ l6)
  coherence-htpy-left-extension-Precategory R S e =
    (x : obj-Precategory C) →
    comp-hom-Precategory D
      ( hom-family-natural-transformation-Precategory C' D (pr1 R) (pr1 S)
        ( natural-transformation-eq-Precategory C' D
          ( extension-left-extension-Precategory R)
          ( extension-left-extension-Precategory S)
          ( e))
        ( obj-functor-Precategory C C' p x))
      ( hom-family-left-extension-Precategory R x) ＝
    hom-family-left-extension-Precategory S x

  htpy-left-extension-Precategory :
    (R S : left-extension-Precategory) →
    UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  htpy-left-extension-Precategory R S =
    Σ ( extension-left-extension-Precategory R ＝
        extension-left-extension-Precategory S)
      ( coherence-htpy-left-extension-Precategory R S)

  is-torsorial-htpy-left-extension-Precategory :
    (R : left-extension-Precategory) →
    is-torsorial (htpy-left-extension-Precategory R)
  is-torsorial-htpy-left-extension-Precategory R =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (extension-left-extension-Precategory R))
      ( pair (extension-left-extension-Precategory R) refl)
      ( is-contr-equiv
        ( Σ
          ( natural-transformation-Precategory C D
            ( F)
            ( comp-functor-Precategory C C' D
              ( extension-left-extension-Precategory R) p))
          ( λ τ → τ ＝ natural-transformation-left-extension-Precategory R))
        ( equiv-tot
          ( λ τ →
            inv-equiv
              ( extensionality-natural-transformation-Precategory C D
                ( F)
                ( comp-functor-Precategory C C' D
                  ( extension-left-extension-Precategory R) p)
                _ _) ∘e
            equiv-Π-equiv-family
              ( λ x →
                equiv-inv _ _ ∘e
                equiv-inv-concat (left-unit-law-comp-hom-Precategory D _) _)))
        ( is-torsorial-Id'
          ( natural-transformation-left-extension-Precategory R)))

  refl-htpy-left-extension-Precategory :
    (R : left-extension-Precategory) →
    htpy-left-extension-Precategory R R
  pr1 (refl-htpy-left-extension-Precategory R) = refl
  pr2 (refl-htpy-left-extension-Precategory R) x =
    left-unit-law-comp-hom-Precategory D _

  htpy-eq-left-extension-Precategory :
    (R S : left-extension-Precategory) →
    R ＝ S →
    htpy-left-extension-Precategory R S
  htpy-eq-left-extension-Precategory R .R refl =
    refl-htpy-left-extension-Precategory R

  is-equiv-htpy-eq-left-extension-Precategory :
    (R S : left-extension-Precategory) →
    is-equiv (htpy-eq-left-extension-Precategory R S)
  is-equiv-htpy-eq-left-extension-Precategory R =
    fundamental-theorem-id
      ( is-torsorial-htpy-left-extension-Precategory R)
      ( htpy-eq-left-extension-Precategory R)

  equiv-htpy-eq-left-extension-Precategory :
    (R S : left-extension-Precategory) →
    (R ＝ S) ≃ htpy-left-extension-Precategory R S
  pr1 (equiv-htpy-eq-left-extension-Precategory R S) =
    htpy-eq-left-extension-Precategory R S
  pr2 (equiv-htpy-eq-left-extension-Precategory R S) =
    is-equiv-htpy-eq-left-extension-Precategory R S

  eq-htpy-left-extension-Precategory :
    (R S : left-extension-Precategory) →
    htpy-left-extension-Precategory R S →
    R ＝ S
  eq-htpy-left-extension-Precategory R S =
    map-inv-equiv (equiv-htpy-eq-left-extension-Precategory R S)
```

### Self-extensions

In the case of extending a functor along itself, we have distinguished left
extensions: the identity map gives a left extension (with the identity natural
transformation) and we can iterate any left extension `L` to get a left
extension `L²`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  id-left-extension-Precategory : left-extension-Precategory C D D F F
  pr1 id-left-extension-Precategory = id-functor-Precategory D
  pr2 id-left-extension-Precategory =
    id-natural-transformation-Precategory C D F

  square-left-extension-Precategory :
    (L : left-extension-Precategory C D D F F) →
    left-extension-Precategory C D D F F
  pr1 (square-left-extension-Precategory L) =
    comp-functor-Precategory D D D
      ( extension-left-extension-Precategory C D D F F L)
      ( extension-left-extension-Precategory C D D F F L)
  pr2 (square-left-extension-Precategory L) =
    comp-natural-transformation-Precategory C D
      ( F)
      ( comp-functor-Precategory C D D
        ( extension-left-extension-Precategory C D D F F L)
        ( F))
      ( comp-functor-Precategory C D D
        ( comp-functor-Precategory D D D
          ( extension-left-extension-Precategory C D D F F L)
          ( extension-left-extension-Precategory C D D F F L))
        ( F))
      ( left-whisker-natural-transformation-Precategory C D D
        ( F)
        ( comp-functor-Precategory C D D
          ( extension-left-extension-Precategory C D D F F L)
          ( F))
        ( extension-left-extension-Precategory C D D F F L)
        ( natural-transformation-left-extension-Precategory C D D F F L))
      ( natural-transformation-left-extension-Precategory C D D F F L)
```

## See also

- [Right extensions](category-theory.right-extensions-precategories.md) for the
  dual concept.
