# Colimits in precategories

```agda
module category-theory.colimits-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cocones-precategories
open import category-theory.constant-functors
open import category-theory.functors-precategories
open import category-theory.left-extensions-precategories
open import category-theory.left-kan-extensions-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.terminal-category

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.homotopies
```

</details>

## Idea

A
{{#concept "colimit" Disambiguation="of a functor of precategories" Agda=colimit-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F` between
[precategories](category-theory.precategories.md) is a colimiting
[cocone](category-theory.cocones-precategories.md) under `F`. That is, a cocone
`τ` such that `cocone-map-Precategory C D F τ d` is an
[equivalence](foundation-core.equivalences.md) for all `d : obj-Precategory D`.

Equivalently, the colimit of `F` is a
[left kan extension](category-theory.left-kan-extensions-precategories.md) of
`F` along the terminal functor into the
[terminal precategory](category-theory.terminal-category.md).

We show that both definitions coincide, and we will use the definition using
colimiting cocones as our official one.

If a colimit exists, we call the vertex of the colimiting cocone the **vertex**
of the colimit.

## Definitions

### Colimiting cocones

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-colimit-cocone-Precategory :
    cocone-Precategory C D F → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-colimit-cocone-Precategory τ =
    (d : obj-Precategory D) →
    is-equiv (cocone-map-Precategory C D F τ d)

  colimit-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  colimit-Precategory =
    Σ ( cocone-Precategory C D F)
      ( is-colimit-cocone-Precategory)

  cocone-colimit-Precategory :
    colimit-Precategory →
    cocone-Precategory C D F
  cocone-colimit-Precategory = pr1

  vertex-colimit-Precategory :
    colimit-Precategory →
    obj-Precategory D
  vertex-colimit-Precategory τ =
    vertex-cocone-Precategory C D F (cocone-colimit-Precategory τ)

  is-colimit-colimit-Precategory :
    (τ : colimit-Precategory) →
    is-colimit-cocone-Precategory (cocone-colimit-Precategory τ)
  is-colimit-colimit-Precategory = pr2

  hom-cocone-colimit-Precategory :
    (τ : colimit-Precategory) →
    (φ : cocone-Precategory C D F) →
    hom-Precategory D
      ( vertex-colimit-Precategory τ)
      ( vertex-cocone-Precategory C D F φ)
  hom-cocone-colimit-Precategory τ φ =
    map-inv-is-equiv
      ( is-colimit-colimit-Precategory τ
        ( vertex-cocone-Precategory C D F φ))
      ( natural-transformation-cocone-Precategory C D F φ)
```

### Colimits through left kan extensions

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-colimit-left-extension-Precategory :
    left-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-colimit-left-extension-Precategory =
    is-left-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F

  colimit-Precategory' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  colimit-Precategory' =
    left-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F

module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D) (L : colimit-Precategory' C D F)
  where

  left-extension-colimit-Precategory' :
    left-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
  left-extension-colimit-Precategory' =
    left-extension-left-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L

  extension-colimit-Precategory' :
    functor-Precategory terminal-Precategory D
  extension-colimit-Precategory' =
    extension-left-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L
```

## Properties

### Being a colimit is a property

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-prop-is-colimit-cocone-Precategory :
    (τ : cocone-Precategory C D F) →
    is-prop (is-colimit-cocone-Precategory C D F τ)
  is-prop-is-colimit-cocone-Precategory τ =
    is-prop-Π (λ φ → is-property-is-equiv _)

  is-prop-is-colimit-Precategory' :
    ( R : left-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F) →
    is-prop (is-colimit-left-extension-Precategory C D F R)
  is-prop-is-colimit-Precategory' R =
    is-prop-Π (λ K → is-property-is-equiv _)
```

### Colimiting cocones are equivalent to colimits

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  equiv-is-left-kan-extension-is-colimit-Precategory :
    (τ : cocone-Precategory C D F) →
    is-colimit-cocone-Precategory C D F τ ≃
    is-left-kan-extension-Precategory C terminal-Precategory D
      ( terminal-functor-Precategory C)
      ( F)
      ( map-equiv (equiv-left-extension-cocone-Precategory C D F) τ)
  equiv-is-left-kan-extension-is-colimit-Precategory τ =
    equiv-Π _
      ( equiv-point-Precategory D)
      ( λ x →
        equiv-iff-is-prop
          ( is-property-is-equiv _)
          ( is-property-is-equiv _)
          ( λ e →
            is-equiv-left-factor
              ( induced-left-extension-map x)
              ( natural-transformation-constant-functor-Precategory
                ( terminal-Precategory)
                ( D))
              ( tr is-equiv (inv (lemma τ x)) e)
              ( is-equiv-natural-transformation-constant-functor-Precategory
                ( D)
                ( _)
                ( _)))
          ( λ e →
            tr is-equiv (lemma τ x)
              ( is-equiv-comp
                ( induced-left-extension-map x)
                ( natural-transformation-constant-functor-Precategory
                  ( terminal-Precategory)
                  ( D))
                ( is-equiv-natural-transformation-constant-functor-Precategory
                  ( D)
                  ( _)
                  ( _))
                ( e))))
    where
      induced-left-extension-map :
        ( x : obj-Precategory D) →
        natural-transformation-Precategory terminal-Precategory D
          ( extension-left-extension-Precategory C terminal-Precategory D
            ( terminal-functor-Precategory C)
            ( F)
            ( map-equiv (equiv-left-extension-cocone-Precategory C D F) τ))
          ( constant-functor-Precategory terminal-Precategory D x) →
        natural-transformation-Precategory C D F
          ( comp-functor-Precategory C terminal-Precategory D
            ( constant-functor-Precategory terminal-Precategory D x)
            ( terminal-functor-Precategory C))
      induced-left-extension-map x =
        left-extension-map-Precategory C terminal-Precategory D
          ( terminal-functor-Precategory C) ( F)
          ( map-equiv (equiv-left-extension-cocone-Precategory C D F) τ)
          ( constant-functor-Precategory terminal-Precategory D x)
      lemma :
        ( τ : cocone-Precategory C D F)
        ( x : obj-Precategory D) →
        ( left-extension-map-Precategory C terminal-Precategory D
          ( terminal-functor-Precategory C) F
          ( map-equiv (equiv-left-extension-cocone-Precategory C D F) τ)
          ( constant-functor-Precategory terminal-Precategory D x)) ∘
        ( natural-transformation-constant-functor-Precategory
          terminal-Precategory D) ＝
        ( cocone-map-Precategory C D F τ x)
      lemma τ x =
        eq-htpy
          ( λ f →
            eq-htpy-hom-family-natural-transformation-Precategory C D
              ( F)
              ( comp-functor-Precategory C terminal-Precategory D
                ( point-Precategory D x)
                ( terminal-functor-Precategory C))
              ( _)
              ( _)
              ( refl-htpy))

  equiv-colimit-colimit'-Precategory :
    colimit-Precategory C D F ≃ colimit-Precategory' C D F
  equiv-colimit-colimit'-Precategory =
    equiv-Σ
      ( is-left-kan-extension-Precategory C terminal-Precategory D
        ( terminal-functor-Precategory C) F)
      ( equiv-left-extension-cocone-Precategory C D F)
      ( λ τ → equiv-is-left-kan-extension-is-colimit-Precategory τ)

  colimit-colimit'-Precategory :
    colimit-Precategory C D F → colimit-Precategory' C D F
  colimit-colimit'-Precategory =
    map-equiv equiv-colimit-colimit'-Precategory

  colimit'-colimit-Precategory :
    colimit-Precategory' C D F → colimit-Precategory C D F
  colimit'-colimit-Precategory =
    map-inv-equiv equiv-colimit-colimit'-Precategory
```

## See also

- [Limits](category-theory.limits-precategories.md) for the dual concept.
