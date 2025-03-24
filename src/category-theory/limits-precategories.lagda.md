# Limits in precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.limits-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategories funext univalence truncations
open import category-theory.constant-functors funext univalence truncations
open import category-theory.functors-precategories funext univalence truncations
open import category-theory.natural-transformations-functors-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations
open import category-theory.right-extensions-precategories funext univalence truncations
open import category-theory.right-kan-extensions-precategories funext univalence truncations
open import category-theory.terminal-category funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.function-extensionality funext
open import foundation.function-types funext
open import foundation.functoriality-dependent-function-types funext univalence
open import foundation.functoriality-dependent-pair-types funext
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.propositions funext univalence
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "limit" Disambiguation="of a functor of precategories" Agda=limit-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F` between
[precategories](category-theory.precategories.md) is a limiting
[cone](category-theory.cones-precategories.md) over `F`. That is, a cone `τ`
such that `cone-map-Precategory C D F τ d` is an equivalence for all
`d : obj-Precategory D`.

Equivalently, the limit of `F` is a
[right kan extension](category-theory.right-kan-extensions-precategories.md) of
`F` along the terminal functor into the
[terminal precategory](category-theory.terminal-category.md).

We show that both definitions coincide, and we will use the definition using
limiting cones as our official one.

If a limit exists, we call the vertex of the limiting cone the **vertex** of the
limit.

## Definition

### Limiting cones

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-limiting-cone-Precategory :
    cone-Precategory C D F → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-limiting-cone-Precategory τ =
    (d : obj-Precategory D) →
    is-equiv (cone-map-Precategory C D F τ d)

  limit-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  limit-Precategory =
    Σ ( cone-Precategory C D F)
      ( is-limiting-cone-Precategory)

  cone-limit-Precategory :
    limit-Precategory →
    cone-Precategory C D F
  cone-limit-Precategory = pr1

  vertex-limit-Precategory :
    limit-Precategory →
    obj-Precategory D
  vertex-limit-Precategory τ =
    vertex-cone-Precategory C D F (cone-limit-Precategory τ)

  is-limiting-limit-Precategory :
    (τ : limit-Precategory) →
    is-limiting-cone-Precategory (cone-limit-Precategory τ)
  is-limiting-limit-Precategory = pr2

  hom-cone-limit-Precategory :
    (τ : limit-Precategory) →
    (φ : cone-Precategory C D F) →
    hom-Precategory D
      ( vertex-cone-Precategory C D F φ)
      ( vertex-limit-Precategory τ)
  hom-cone-limit-Precategory τ φ =
    map-inv-is-equiv
      ( is-limiting-limit-Precategory τ
        ( vertex-cone-Precategory C D F φ))
      ( natural-transformation-cone-Precategory C D F φ)
```

### Limits through right kan extensions

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-limit-right-extension-Precategory :
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-limit-right-extension-Precategory =
    is-right-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F

  limit-Precategory' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  limit-Precategory' =
    right-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F

module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D) (L : limit-Precategory' C D F)
  where

  right-extension-limit-Precategory' :
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
  right-extension-limit-Precategory' =
    right-extension-right-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L

  extension-limit-Precategory' :
    functor-Precategory terminal-Precategory D
  extension-limit-Precategory' =
    extension-right-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L
```

## Properties

### Being a limit is a property

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-prop-is-limiting-cone-Precategory :
    (τ : cone-Precategory C D F) →
    is-prop (is-limiting-cone-Precategory C D F τ)
  is-prop-is-limiting-cone-Precategory τ =
    is-prop-Π λ φ → is-property-is-equiv _

  is-prop-is-limit-Precategory' :
    ( R : right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F) →
    is-prop (is-limit-right-extension-Precategory C D F R)
  is-prop-is-limit-Precategory' R =
    is-prop-Π λ K → is-property-is-equiv _
```

### Limiting cones are equivalent to limits

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  equiv-is-right-kan-extension-is-limiting-Precategory :
    (τ : cone-Precategory C D F) →
    is-limiting-cone-Precategory C D F τ ≃
      is-right-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
      (map-equiv (equiv-right-extension-cone-Precategory C D F) τ)
  equiv-is-right-kan-extension-is-limiting-Precategory τ =
    equiv-Π _
      ( equiv-point-Precategory D)
      ( λ x →
        equiv-iff-is-prop
          ( is-property-is-equiv _)
          ( is-property-is-equiv _)
          ( λ e →
            is-equiv-left-factor
            ( induced-right-extension-map x)
            ( natural-transformation-constant-functor-Precategory
              terminal-Precategory D)
            ( tr is-equiv (inv (lemma τ x)) e)
            ( is-equiv-natural-transformation-constant-functor-Precategory
              D _ _))
          ( λ e →
            tr is-equiv (lemma τ x)
              ( is-equiv-comp
                ( induced-right-extension-map x)
                ( natural-transformation-constant-functor-Precategory
                  terminal-Precategory D)
                ( is-equiv-natural-transformation-constant-functor-Precategory
                  D _ _)
                ( e))))
    where
      induced-right-extension-map = λ x →
        right-extension-map-Precategory C terminal-Precategory D
          ( terminal-functor-Precategory C) ( F)
          ( map-equiv (equiv-right-extension-cone-Precategory C D F) τ)
          ( constant-functor-Precategory terminal-Precategory D x)
      lemma :
        ( τ : cone-Precategory C D F)
        ( x : obj-Precategory D) →
          ( right-extension-map-Precategory C terminal-Precategory D
            ( terminal-functor-Precategory C) F
            ( map-equiv (equiv-right-extension-cone-Precategory C D F) τ)
            ( constant-functor-Precategory terminal-Precategory D x)) ∘
          ( natural-transformation-constant-functor-Precategory
            terminal-Precategory D) ＝
        ( cone-map-Precategory C D F τ x)
      lemma τ x =
        eq-htpy λ f →
          eq-htpy-hom-family-natural-transformation-Precategory C D
            ( comp-functor-Precategory C terminal-Precategory D
              ( point-Precategory D x)
              ( terminal-functor-Precategory C))
            ( F)
            ( _)
            ( _)
            ( λ g → refl)

  equiv-limit-limit'-Precategory :
    limit-Precategory C D F ≃ limit-Precategory' C D F
  equiv-limit-limit'-Precategory =
    equiv-Σ
      ( is-right-kan-extension-Precategory C terminal-Precategory D
        ( terminal-functor-Precategory C) F)
      ( equiv-right-extension-cone-Precategory C D F)
      ( λ τ → equiv-is-right-kan-extension-is-limiting-Precategory τ)

  limit-limit'-Precategory :
    limit-Precategory C D F → limit-Precategory' C D F
  limit-limit'-Precategory =
    map-equiv equiv-limit-limit'-Precategory

  limit'-limit-Precategory :
    limit-Precategory' C D F → limit-Precategory C D F
  limit'-limit-Precategory =
    map-inv-equiv equiv-limit-limit'-Precategory
```
