# Cones in precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.cones-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories funext univalence truncations
open import category-theory.commuting-triangles-of-morphisms-in-precategories funext univalence truncations
open import category-theory.constant-functors funext univalence truncations
open import category-theory.functors-precategories funext univalence truncations
open import category-theory.maps-precategories funext univalence truncations
open import category-theory.natural-transformations-functors-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations
open import category-theory.precategory-of-functors funext univalence truncations
open import category-theory.right-extensions-precategories funext univalence truncations
open import category-theory.terminal-category funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.contractible-types funext univalence
open import foundation.dependent-identifications funext
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.equality-dependent-function-types funext
open import foundation.equality-dependent-pair-types funext
open import foundation.equivalences funext
open import foundation.function-extensionality funext
open import foundation.function-types funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.functoriality-dependent-pair-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies funext
open import foundation.homotopy-induction funext
open import foundation.identity-types funext
open import foundation.multivariable-homotopies funext
open import foundation.propositions funext univalence
open import foundation.retractions funext
open import foundation.sections funext
open import foundation.sets funext univalence
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "cone" Disambiguation="over a functor between precategories" Agda=cone-Precategory}}
over a [functor](category-theory.functors-precategories.md) `F` between
[precategories](category-theory.precategories.md) is a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
from a [constant functor](category-theory.constant-functors.md) to `F`.

In this context, we usually think of (and refer to) the functor `F` as a
**diagram** in its codomain, A cone over such diagram then corresponds to an
element `d`, called the **vertex** of the cone, equipped with components
`d → F x` satisfying the naturality condition.

For example, if `F` corresponds to the diagram `F x → F y`, then a cone over `F`
corresponds to a commuting triangle as below.

```text
      d
    /   \
   /     \
  ∨       ∨
 Fx ----> Fy
```

Equivalently, we can see a cone over `F` as a
[right extension](category-theory.right-extensions-precategories.md) of `F`
along the terminal functor into the
[terminal precategory](category-theory.terminal-category.md).

## Definitions

### The type of cones over a functor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  cone-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cone-Precategory =
    Σ ( obj-Precategory D)
      ( λ d →
        natural-transformation-Precategory C D
          ( constant-functor-Precategory C D d)
          ( F))

  make-cone-Precategory :
    ( d : obj-Precategory D)
    ( α :
      ( x : obj-Precategory C) →
      ( hom-Precategory D d (obj-functor-Precategory C D F x))) →
    ( {x y : obj-Precategory C} (f : hom-Precategory C x y) →
      coherence-triangle-hom-Precategory D
        ( α x)
        ( α y)
        ( hom-functor-Precategory C D F f)) →
    cone-Precategory
  pr1 (make-cone-Precategory d α p) = d
  pr1 (pr2 (make-cone-Precategory d α p)) = α
  pr2 (pr2 (make-cone-Precategory d α p)) f =
    inv (p f) ∙ inv (right-unit-law-comp-hom-Precategory D _)

  vertex-cone-Precategory : cone-Precategory → obj-Precategory D
  vertex-cone-Precategory = pr1

  vertex-functor-cone-Precategory :
    cone-Precategory → functor-Precategory C D
  vertex-functor-cone-Precategory α =
    constant-functor-Precategory C D (vertex-cone-Precategory α)

  natural-transformation-cone-Precategory :
    (α : cone-Precategory) →
    natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
  natural-transformation-cone-Precategory = pr2

  component-cone-Precategory :
    (α : cone-Precategory) (x : obj-Precategory C) →
    hom-Precategory D
      ( vertex-cone-Precategory α)
      ( obj-functor-Precategory C D F x)
  component-cone-Precategory α =
    hom-family-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
      ( natural-transformation-cone-Precategory α)

  naturality-cone-Precategory :
    (α : cone-Precategory) {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    coherence-triangle-hom-Precategory D
      ( component-cone-Precategory α x)
      ( component-cone-Precategory α y)
      ( hom-functor-Precategory C D F f)
  naturality-cone-Precategory α {x} {y} f =
    inv (right-unit-law-comp-hom-Precategory D _) ∙
    inv
      ( naturality-natural-transformation-Precategory C D
        ( vertex-functor-cone-Precategory α)
        ( F)
        ( natural-transformation-cone-Precategory α)
        ( f))
```

### Precomposing cones

```agda
  cone-map-Precategory :
    (τ : cone-Precategory)
    (d : obj-Precategory D) →
    (hom-Precategory D d (vertex-cone-Precategory τ)) →
    natural-transformation-Precategory C D
      ( constant-functor-Precategory C D d)
      ( F)
  pr1 (cone-map-Precategory τ d f) x =
    comp-hom-Precategory D (component-cone-Precategory τ x) f
  pr2 (cone-map-Precategory τ d f) h =
    inv (associative-comp-hom-Precategory D _ _ _) ∙
    ap
      ( λ g → comp-hom-Precategory D g f)
      ( inv (naturality-cone-Precategory τ h)) ∙
    inv (right-unit-law-comp-hom-Precategory D _)
```

## Properties

### Characterization of equality of cones over functors between precategories

```agda
  coherence-htpy-cone-Precategory :
    (α β : cone-Precategory) →
    (p : vertex-cone-Precategory α ＝ vertex-cone-Precategory β) →
    UU (l1 ⊔ l4)
  coherence-htpy-cone-Precategory α β p =
    (x : obj-Precategory C) →
    coherence-triangle-hom-Precategory D
      ( hom-eq-Precategory D
        ( vertex-cone-Precategory α)
        ( vertex-cone-Precategory β)
        ( p))
      ( component-cone-Precategory α x)
      ( component-cone-Precategory β x)

  htpy-cone-Precategory :
    (α β : cone-Precategory) →
    UU (l1 ⊔ l3 ⊔ l4)
  htpy-cone-Precategory α β =
    Σ ( vertex-cone-Precategory α ＝ vertex-cone-Precategory β)
      ( coherence-htpy-cone-Precategory α β)

  refl-htpy-cone-Precategory :
    (α : cone-Precategory) →
    htpy-cone-Precategory α α
  pr1 (refl-htpy-cone-Precategory α) = refl
  pr2 (refl-htpy-cone-Precategory α) x =
    inv (right-unit-law-comp-hom-Precategory D _)

  htpy-eq-cone-Precategory :
    (α β : cone-Precategory) →
    α ＝ β →
    htpy-cone-Precategory α β
  htpy-eq-cone-Precategory α .α refl = refl-htpy-cone-Precategory α

  is-torsorial-htpy-cone-Precategory :
    (α : cone-Precategory) →
    is-torsorial (htpy-cone-Precategory α)
  is-torsorial-htpy-cone-Precategory α =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (vertex-cone-Precategory α))
      ( pair (vertex-cone-Precategory α) refl)
      ( is-contr-equiv
        ( Σ
          ( natural-transformation-Precategory C D
            ( constant-functor-Precategory C D (vertex-cone-Precategory α)) F)
              (λ τ → τ ＝ (natural-transformation-cone-Precategory α)))
        ( equiv-tot
          ( λ τ →
            inv-equiv
              ( extensionality-natural-transformation-Precategory C D
                ( constant-functor-Precategory C D (vertex-cone-Precategory α))
                ( F) _ _) ∘e
            equiv-Π-equiv-family
              ( λ x →
                equiv-inv (component-cone-Precategory α x) (pr1 τ x) ∘e
                equiv-concat'
                  ( component-cone-Precategory α x)
                  ( right-unit-law-comp-hom-Precategory D _))))
        ( is-torsorial-Id' (natural-transformation-cone-Precategory α)))

  is-equiv-htpy-eq-cone-Precategory :
    (α β : cone-Precategory) →
    is-equiv (htpy-eq-cone-Precategory α β)
  is-equiv-htpy-eq-cone-Precategory α =
    fundamental-theorem-id
      ( is-torsorial-htpy-cone-Precategory α)
      ( htpy-eq-cone-Precategory α)

  equiv-htpy-eq-cone-Precategory :
    (α β : cone-Precategory) →
    (α ＝ β) ≃ htpy-cone-Precategory α β
  pr1 (equiv-htpy-eq-cone-Precategory α β) = htpy-eq-cone-Precategory α β
  pr2 (equiv-htpy-eq-cone-Precategory α β) =
    is-equiv-htpy-eq-cone-Precategory α β

  eq-htpy-cone-Precategory :
    (α β : cone-Precategory) →
    htpy-cone-Precategory α β →
    α ＝ β
  eq-htpy-cone-Precategory α β =
    map-inv-equiv (equiv-htpy-eq-cone-Precategory α β)
```

### A cone is a right extension along the terminal map

```agda
  equiv-right-extension-cone-Precategory :
    cone-Precategory ≃
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
  equiv-right-extension-cone-Precategory =
    equiv-Σ-equiv-base
    ( λ K → natural-transformation-Precategory C D
      ( comp-functor-Precategory C terminal-Precategory D
        ( K)
        ( terminal-functor-Precategory C))
      ( F))
    ( equiv-point-Precategory D)

  right-extension-cone-Precategory :
    cone-Precategory →
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
  right-extension-cone-Precategory =
    map-equiv equiv-right-extension-cone-Precategory

  cone-right-extension-Precategory :
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F →
    cone-Precategory
  cone-right-extension-Precategory =
    map-inv-equiv equiv-right-extension-cone-Precategory

  vertex-right-extension-Precategory :
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F →
    obj-Precategory D
  vertex-right-extension-Precategory R =
    vertex-cone-Precategory
      ( cone-right-extension-Precategory R)
```
