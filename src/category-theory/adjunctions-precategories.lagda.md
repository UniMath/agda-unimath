# Adjunctions between precategories

```agda
module category-theory.adjunctions-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
```

</details>
## Idea

Let `C` and `D` be two [precategories](category-theory.precategories.md). Two
[functors](category-theory.functors-precategories.md) `L : C → D` and
`R : D → C` constitute an **adjoint pair** if

- for each pair of objects `X` in `C` and `Y` in `D`, there is an
  [equivalence](foundation-core.equivalences.md)
  `ϕ X Y : hom (L X) Y ≃ hom X (R Y)` such that
- for every pair of morphisms `f : X₂ → X₁` and `g : Y₁ → Y₂` the following
  square commutes:

```text
                       ϕ X₁ Y₁
        hom (L X₁) Y₁ --------> hom X₁ (R Y₁)
              |                       |
  g ∘ - ∘ L f |                       | R g ∘ - ∘ f
              |                       |
              ∨                       ∨
        hom (L X₂) Y₂ --------> hom X₂ (R Y₂)
                       ϕ X₂ Y₂
```

In this case we say that `L` is **left adjoint** to `R` and `R` is **right
adjoint** to `L`, and write this as `L ⊣ R`.

## Definitions

### The predicate of being an adjoint pair of functors

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (L : functor-Precategory C D)
  (R : functor-Precategory D C)
  where

  family-of-equivalences-adjoint-pair-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  family-of-equivalences-adjoint-pair-Precategory =
    (x : obj-Precategory C) (y : obj-Precategory D) →
    hom-Precategory D (obj-functor-Precategory C D L x) y ≃
    hom-Precategory C x (obj-functor-Precategory D C R y)

  naturality-family-of-equivalences-adjoint-pair-Precategory :
    family-of-equivalences-adjoint-pair-Precategory → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  naturality-family-of-equivalences-adjoint-pair-Precategory e =
    {x1 x2 : obj-Precategory C} {y1 y2 : obj-Precategory D}
    (f : hom-Precategory C x2 x1) (g : hom-Precategory D y1 y2) →
    coherence-square-maps
      ( map-equiv (e x1 y1))
      ( λ h →
        comp-hom-Precategory D
          ( comp-hom-Precategory D g h)
          ( hom-functor-Precategory C D L f))
      ( λ h →
        comp-hom-Precategory C
          ( comp-hom-Precategory C
            ( hom-functor-Precategory D C R g)
            ( h))
          ( f))
      ( map-equiv (e x2 y2))

  is-adjoint-pair-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-adjoint-pair-Precategory =
    Σ ( family-of-equivalences-adjoint-pair-Precategory)
      ( λ e → naturality-family-of-equivalences-adjoint-pair-Precategory e)

  equiv-is-adjoint-pair-Precategory :
    is-adjoint-pair-Precategory →
    family-of-equivalences-adjoint-pair-Precategory
  equiv-is-adjoint-pair-Precategory = pr1

  naturality-equiv-is-adjoint-pair-Precategory :
    (H : is-adjoint-pair-Precategory) →
    naturality-family-of-equivalences-adjoint-pair-Precategory
      ( equiv-is-adjoint-pair-Precategory H)
  naturality-equiv-is-adjoint-pair-Precategory = pr2

  map-equiv-is-adjoint-pair-Precategory :
    is-adjoint-pair-Precategory →
    (x : obj-Precategory C) (y : obj-Precategory D) →
    hom-Precategory D (obj-functor-Precategory C D L x) y →
    hom-Precategory C x (obj-functor-Precategory D C R y)
  map-equiv-is-adjoint-pair-Precategory H X Y =
    map-equiv (equiv-is-adjoint-pair-Precategory H X Y)
```

## Adjunctions between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  Adjunction-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  Adjunction-Precategory =
    Σ ( (functor-Precategory C D) × (functor-Precategory D C))
      ( λ LR → is-adjoint-pair-Precategory C D (pr1 LR) (pr2 LR))

  make-Adjunction-Precategory :
    (L : functor-Precategory C D) (R : functor-Precategory D C)
    (a : is-adjoint-pair-Precategory C D L R) →
    Adjunction-Precategory
  make-Adjunction-Precategory L R a = (L , R) , a
```

### Triangle identities

Equivalently, two functors `L` and `R` are an adjoint pair if there is a natural
transformation `η : id ⇒ RL` called the **unit** and a natural transformation
`ε : LR ⇒ id` called the **counit** satisfying two **triangle identities**:

```text
  εL ∘ Lη = id
  Rε ∘ ηR = id
```

Here, we interpret the equality above as a homotopy of natural transformations
to avoid associativity issues.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (L : functor-Precategory C D)
  (R : functor-Precategory D C)
  (let LR = comp-functor-Precategory D C D L R)
  (let RL = comp-functor-Precategory C D C R L)
  (let idC = id-functor-Precategory C)
  (let idD = id-functor-Precategory D)
  (η : natural-transformation-Precategory C C idC RL)
  (ε : natural-transformation-Precategory D D LR idD)
  (let η₀ = hom-family-natural-transformation-Precategory C C idC RL η)
  (let ε₀ = hom-family-natural-transformation-Precategory D D LR idD ε)
  (let L₀ = obj-functor-Precategory C D L)
  (let L₁ = hom-functor-Precategory C D L)
  (let R₀ = obj-functor-Precategory D C R)
  (let R₁ = hom-functor-Precategory D C R)
  where

  has-left-triangle-identity-Precategory : UU (l1 ⊔ l4)
  has-left-triangle-identity-Precategory =
    (x : obj-Precategory C) →
    comp-hom-Precategory D (ε₀ (L₀ x)) (L₁ (η₀ x)) ＝ id-hom-Precategory D

  has-right-triangle-identity-Precategory : UU (l2 ⊔ l3)
  has-right-triangle-identity-Precategory =
    (y : obj-Precategory D) →
    ( comp-hom-Precategory C
      ( R₁ (ε₀ y))
      ( η₀ (R₀ y))) ＝
    ( id-hom-Precategory C)

  module _
    (lt : has-left-triangle-identity-Precategory)
    (rt : has-right-triangle-identity-Precategory)
    (x : obj-Precategory C) (y : obj-Precategory D)
    where

    map-sharp-unit-counit-Precategory :
      hom-Precategory D (L₀ x) y →
      hom-Precategory C x (R₀ y)
    map-sharp-unit-counit-Precategory g =
      comp-hom-Precategory C (R₁ g) (η₀ x)

    map-flat-unit-counit-Precategory :
      hom-Precategory C x (R₀ y) →
      hom-Precategory D (L₀ x) y
    map-flat-unit-counit-Precategory f =
      comp-hom-Precategory D (ε₀ y) (L₁ f)

    is-section-map-flat-unit-counit-Precategory :
      is-section
        map-sharp-unit-counit-Precategory
        map-flat-unit-counit-Precategory
    is-section-map-flat-unit-counit-Precategory f =
      ( ap
        ( precomp-hom-Precategory C (η₀ x) _)
        ( preserves-comp-functor-Precategory D C R (ε₀ y) (L₁ f))) ∙
      ( associative-comp-hom-Precategory C (R₁ (ε₀ y)) (R₁ (L₁ f)) (η₀ x)) ∙
      ( ap
        ( postcomp-hom-Precategory C (R₁ (ε₀ y)) _)
        ( naturality-natural-transformation-Precategory C C
          ( id-functor-Precategory C) RL η f)) ∙
      ( inv
        ( associative-comp-hom-Precategory C (R₁ (ε₀ y)) (η₀ (R₀ y)) f)) ∙
      ( ap (precomp-hom-Precategory C f _) (rt y)) ∙
      ( left-unit-law-comp-hom-Precategory C f)

    is-retraction-map-flat-unit-counit-Precategory :
      is-retraction
        map-sharp-unit-counit-Precategory
        map-flat-unit-counit-Precategory
    is-retraction-map-flat-unit-counit-Precategory g =
      ( ap
        ( postcomp-hom-Precategory D (ε₀ y) _)
        ( preserves-comp-functor-Precategory C D L (R₁ g) (η₀ x))) ∙
      ( inv
        ( associative-comp-hom-Precategory D
          ( ε₀ y)
          ( L₁ (R₁ g))
          ( L₁ (η₀ x)))) ∙
      ( ap
        ( precomp-hom-Precategory D (L₁ (η₀ x)) _)
        ( inv
          ( naturality-natural-transformation-Precategory D D
            ( LR)
            ( id-functor-Precategory D) ε g))) ∙
      ( associative-comp-hom-Precategory D g (ε₀ (L₀ x)) (L₁ (η₀ x))) ∙
      ( ap (postcomp-hom-Precategory D g _) (lt x)) ∙
      ( right-unit-law-comp-hom-Precategory D g)

    section-sharp-unit-counit-Precategory :
      section map-sharp-unit-counit-Precategory
    section-sharp-unit-counit-Precategory =
      ( map-flat-unit-counit-Precategory ,
        is-section-map-flat-unit-counit-Precategory)

    retraction-sharp-unit-counit-Precategory :
      retraction map-sharp-unit-counit-Precategory
    retraction-sharp-unit-counit-Precategory =
      ( map-flat-unit-counit-Precategory ,
        is-retraction-map-flat-unit-counit-Precategory)

    is-equiv-sharp-unit-counit-Precategory :
      is-equiv map-sharp-unit-counit-Precategory
    is-equiv-sharp-unit-counit-Precategory =
      ( section-sharp-unit-counit-Precategory ,
        retraction-sharp-unit-counit-Precategory)

  module _
    (lt : has-left-triangle-identity-Precategory)
    (rt : has-right-triangle-identity-Precategory)
    where

    equiv-family-unit-counit-Precategory :
      family-of-equivalences-adjoint-pair-Precategory C D L R
    equiv-family-unit-counit-Precategory x y =
      ( map-sharp-unit-counit-Precategory lt rt x y ,
        is-equiv-sharp-unit-counit-Precategory lt rt x y)

    naturality-equiv-family-unit-counit-Precategory :
      naturality-family-of-equivalences-adjoint-pair-Precategory C D L R
        equiv-family-unit-counit-Precategory
    naturality-equiv-family-unit-counit-Precategory
      {x1} {x2} {y1} {y2} f g h =
      ( ap
        ( precomp-hom-Precategory C (η₀ x2) _)
        ( ( preserves-comp-functor-Precategory D C R
            ( comp-hom-Precategory D g h)
            ( L₁ f)) ∙
          ( ap
            ( precomp-hom-Precategory C (R₁ (L₁ f)) _)
            ( preserves-comp-functor-Precategory D C R g h)))) ∙
      ( associative-comp-hom-Precategory C _ (R₁ (L₁ f)) (η₀ x2)) ∙
      ( ap
        ( postcomp-hom-Precategory C _ _)
        ( naturality-natural-transformation-Precategory C C idC RL η f)) ∙
      ( inv (associative-comp-hom-Precategory C _ (η₀ x1) f)) ∙
      ( ap
        ( precomp-hom-Precategory C f _)
        ( associative-comp-hom-Precategory C _ _ _))

    is-adjoint-pair-unit-counit-Precategory :
      is-adjoint-pair-Precategory C D L R
    is-adjoint-pair-unit-counit-Precategory =
      ( equiv-family-unit-counit-Precategory ,
        naturality-equiv-family-unit-counit-Precategory)
```
