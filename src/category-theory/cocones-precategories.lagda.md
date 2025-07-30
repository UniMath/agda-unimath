# Cocones in precategories

```agda
module category-theory.cocones-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.commuting-triangles-of-morphisms-in-precategories
open import category-theory.constant-functors
open import category-theory.functors-precategories
open import category-theory.left-extensions-precategories
open import category-theory.maps-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors
open import category-theory.terminal-category

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
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
```

</details>

## Idea

A
{{#concept "cocone" Disambiguation="under a functor between precategories" Agda=cocone-Precategory}}
under a [functor](category-theory.functors-precategories.md) `F` between
[precategories](category-theory.precategories.md) is an object `d` of the
codomain together with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
from `F` to the [constant functor](category-theory.constant-functors.md) at `d`.

In this context, we usually think of (and refer to) the functor `F` as a
**diagram** in its codomain, A cocone under such diagram then corresponds to an
element `d`, called the **vertex** of the cocone, equipped with components
`F x → d` satisfying the naturality condition.

For example, if `F` corresponds to the diagram `F x → F y`, then a cocone under
`F` corresponds to a commuting triangle as below.

```text
 Fx ----> Fy
   \     /
    \   /
     ∨ ∨
      d
```

Equivalently, we can see a cocone under `F` as a
[left extension](category-theory.left-extensions-precategories.md) of `F` along
the terminal functor into the
[terminal precategory](category-theory.terminal-category.md).

## Definitions

### The type of cocones under a functor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  cocone-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-Precategory =
    Σ ( obj-Precategory D)
      ( λ d →
        natural-transformation-Precategory C D
          ( F)
          ( constant-functor-Precategory C D d))

  make-cocone-Precategory :
    ( d : obj-Precategory D)
    ( α :
      ( x : obj-Precategory C) →
      ( hom-Precategory D (obj-functor-Precategory C D F x) d)) →
    ( {x y : obj-Precategory C} (f : hom-Precategory C x y) →
      coherence-triangle-hom-Precategory D
        ( hom-functor-Precategory C D F f)
        ( α x)
        ( α y)) →
    cocone-Precategory
  pr1 (make-cocone-Precategory d α p) = d
  pr1 (pr2 (make-cocone-Precategory d α p)) = α
  pr2 (pr2 (make-cocone-Precategory d α p)) f =
    left-unit-law-comp-hom-Precategory D _ ∙ p f

  vertex-cocone-Precategory : cocone-Precategory → obj-Precategory D
  vertex-cocone-Precategory = pr1

  vertex-functor-cocone-Precategory :
    cocone-Precategory → functor-Precategory C D
  vertex-functor-cocone-Precategory α =
    constant-functor-Precategory C D (vertex-cocone-Precategory α)

  natural-transformation-cocone-Precategory :
    (α : cocone-Precategory) →
    natural-transformation-Precategory C D
      ( F)
      ( vertex-functor-cocone-Precategory α)
  natural-transformation-cocone-Precategory = pr2

  component-cocone-Precategory :
    (α : cocone-Precategory) (x : obj-Precategory C) →
    hom-Precategory D
      ( obj-functor-Precategory C D F x)
      ( vertex-cocone-Precategory α)
  component-cocone-Precategory α =
    hom-family-natural-transformation-Precategory C D
      ( F)
      ( vertex-functor-cocone-Precategory α)
      ( natural-transformation-cocone-Precategory α)

  naturality-cocone-Precategory :
    (α : cocone-Precategory) {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    coherence-triangle-hom-Precategory D
      ( hom-functor-Precategory C D F f)
      ( component-cocone-Precategory α x)
      ( component-cocone-Precategory α y)
  naturality-cocone-Precategory α {x} {y} f =
    inv (left-unit-law-comp-hom-Precategory D _) ∙
    naturality-natural-transformation-Precategory C D
      ( F)
      ( vertex-functor-cocone-Precategory α)
      ( natural-transformation-cocone-Precategory α)
      ( f)
```

### Postcomposing cocones

```agda
  cocone-map-Precategory :
    (τ : cocone-Precategory)
    (d : obj-Precategory D) →
    (hom-Precategory D (vertex-cocone-Precategory τ) d) →
    natural-transformation-Precategory C D
      ( F)
      ( constant-functor-Precategory C D d)
  pr1 (cocone-map-Precategory τ d f) x =
    comp-hom-Precategory D f (component-cocone-Precategory τ x)
  pr2 (cocone-map-Precategory τ d f) h =
    ( left-unit-law-comp-hom-Precategory D _) ∙
    ( ap
      ( λ g → comp-hom-Precategory D f g)
      ( naturality-cocone-Precategory τ h)) ∙
    ( inv (associative-comp-hom-Precategory D _ _ _))
```

## Properties

### Characterization of equality of cocones

```agda
  coherence-htpy-cocone-Precategory :
    (α β : cocone-Precategory) →
    (p : vertex-cocone-Precategory α ＝ vertex-cocone-Precategory β) →
    UU (l1 ⊔ l4)
  coherence-htpy-cocone-Precategory α β p =
    (x : obj-Precategory C) →
    coherence-triangle-hom-Precategory D
      ( component-cocone-Precategory α x)
      ( component-cocone-Precategory β x)
      ( hom-eq-Precategory D
        ( vertex-cocone-Precategory α)
        ( vertex-cocone-Precategory β)
        ( p))

  htpy-cocone-Precategory :
    (α β : cocone-Precategory) →
    UU (l1 ⊔ l3 ⊔ l4)
  htpy-cocone-Precategory α β =
    Σ ( vertex-cocone-Precategory α ＝ vertex-cocone-Precategory β)
      ( coherence-htpy-cocone-Precategory α β)

  refl-htpy-cocone-Precategory :
    (α : cocone-Precategory) →
    htpy-cocone-Precategory α α
  pr1 (refl-htpy-cocone-Precategory α) = refl
  pr2 (refl-htpy-cocone-Precategory α) x =
    inv (left-unit-law-comp-hom-Precategory D _)

  htpy-eq-cocone-Precategory :
    (α β : cocone-Precategory) →
    α ＝ β →
    htpy-cocone-Precategory α β
  htpy-eq-cocone-Precategory α .α refl = refl-htpy-cocone-Precategory α

  is-torsorial-htpy-cocone-Precategory :
    (α : cocone-Precategory) →
    is-torsorial (htpy-cocone-Precategory α)
  is-torsorial-htpy-cocone-Precategory α =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (vertex-cocone-Precategory α))
      ( pair (vertex-cocone-Precategory α) refl)
      ( is-contr-equiv
        ( Σ
          ( natural-transformation-Precategory C D
            F (constant-functor-Precategory C D (vertex-cocone-Precategory α)))
              (λ τ → τ ＝ (natural-transformation-cocone-Precategory α)))
        ( equiv-tot
          ( λ τ →
            inv-equiv
              ( extensionality-natural-transformation-Precategory C D
                ( F)
                ( constant-functor-Precategory C D
                  ( vertex-cocone-Precategory α))
                ( _)
                ( _)) ∘e
            equiv-Π-equiv-family
              ( λ x →
                equiv-concat'
                  ( pr1 τ x)
                  ( left-unit-law-comp-hom-Precategory D _))))
        ( is-torsorial-Id' (natural-transformation-cocone-Precategory α)))

  is-equiv-htpy-eq-cocone-Precategory :
    (α β : cocone-Precategory) →
    is-equiv (htpy-eq-cocone-Precategory α β)
  is-equiv-htpy-eq-cocone-Precategory α =
    fundamental-theorem-id
      ( is-torsorial-htpy-cocone-Precategory α)
      ( htpy-eq-cocone-Precategory α)

  equiv-htpy-eq-cocone-Precategory :
    (α β : cocone-Precategory) →
    (α ＝ β) ≃ htpy-cocone-Precategory α β
  pr1 (equiv-htpy-eq-cocone-Precategory α β) = htpy-eq-cocone-Precategory α β
  pr2 (equiv-htpy-eq-cocone-Precategory α β) =
    is-equiv-htpy-eq-cocone-Precategory α β

  eq-htpy-cocone-Precategory :
    (α β : cocone-Precategory) →
    htpy-cocone-Precategory α β →
    α ＝ β
  eq-htpy-cocone-Precategory α β =
    map-inv-equiv (equiv-htpy-eq-cocone-Precategory α β)
```

### A cocone is a left extension along the terminal map

```agda
  equiv-left-extension-cocone-Precategory :
    cocone-Precategory ≃
    left-extension-Precategory C terminal-Precategory D
      ( terminal-functor-Precategory C)
      ( F)
  equiv-left-extension-cocone-Precategory =
    equiv-Σ-equiv-base
      ( λ K →
        natural-transformation-Precategory C D
          ( F)
          ( comp-functor-Precategory C terminal-Precategory D
            ( K)
            ( terminal-functor-Precategory C)))
      ( equiv-point-Precategory D)

  left-extension-cocone-Precategory :
    cocone-Precategory →
    left-extension-Precategory C terminal-Precategory D
      ( terminal-functor-Precategory C)
      ( F)
  left-extension-cocone-Precategory =
    map-equiv equiv-left-extension-cocone-Precategory

  cocone-left-extension-Precategory :
    left-extension-Precategory C terminal-Precategory D
      ( terminal-functor-Precategory C)
      ( F) →
    cocone-Precategory
  cocone-left-extension-Precategory =
    map-inv-equiv equiv-left-extension-cocone-Precategory

  vertex-left-extension-Precategory :
    left-extension-Precategory C terminal-Precategory D
      ( terminal-functor-Precategory C)
      ( F) →
    obj-Precategory D
  vertex-left-extension-Precategory R =
    vertex-cocone-Precategory
      ( cocone-left-extension-Precategory R)
```

## See also

- [Colimits](category-theory.colimits-precategories.md) for universal cocones.
- [Cones](category-theory.cones-precategories.md) for the dual concept.
