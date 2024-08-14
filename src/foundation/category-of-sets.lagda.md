# The category of sets

```agda
module foundation.category-of-sets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.complete-precategories
open import category-theory.cones-precategories
open import category-theory.constant-functors
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.limits-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.right-extensions-precategories
open import category-theory.right-kan-extensions-precategories
open import category-theory.terminal-category

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.isomorphisms-of-sets
open import foundation.multivariable-homotopies
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.functoriality-dependent-pair-types
```

</details>

## Idea

The **category of [sets](foundation-core.sets.md)** consists of sets and
functions. There is a [category](category-theory.categories.md) of sets for each
universe level, and there is a
[large category](category-theory.large-categories.md) of sets.

## Definitions

### The large precategory of sets

```agda
Set-Large-Precategory : Large-Precategory lsuc (_⊔_)
obj-Large-Precategory Set-Large-Precategory = Set
hom-set-Large-Precategory Set-Large-Precategory = hom-set-Set
comp-hom-Large-Precategory Set-Large-Precategory g f = g ∘ f
id-hom-Large-Precategory Set-Large-Precategory = id
involutive-eq-associative-comp-hom-Large-Precategory Set-Large-Precategory
  h g f =
  reflⁱ
left-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = refl
right-unit-law-comp-hom-Large-Precategory Set-Large-Precategory f = refl
```

### The large category of sets

```agda
id-iso-Set :
  {l : Level} {X : obj-Large-Precategory Set-Large-Precategory l} →
  iso-Large-Precategory Set-Large-Precategory X X
id-iso-Set {l} {X} = id-iso-Large-Precategory (Set-Large-Precategory) {l} {X}

iso-eq-Set :
  {l : Level} (X Y : obj-Large-Precategory Set-Large-Precategory l) →
  X ＝ Y → iso-Large-Precategory Set-Large-Precategory X Y
iso-eq-Set = iso-eq-Large-Precategory Set-Large-Precategory

is-large-category-Set-Large-Precategory :
  is-large-category-Large-Precategory Set-Large-Precategory
is-large-category-Set-Large-Precategory {l} X =
  fundamental-theorem-id
    ( is-contr-equiv'
      ( Σ (Set l) (equiv-Set X))
      ( equiv-tot (equiv-iso-equiv-Set X))
      ( is-torsorial-equiv-Set X))
    ( iso-eq-Set X)

Set-Large-Category : Large-Category lsuc (_⊔_)
large-precategory-Large-Category Set-Large-Category = Set-Large-Precategory
is-large-category-Large-Category Set-Large-Category =
  is-large-category-Set-Large-Precategory
```

### The precategory of small sets

```agda
Set-Precategory : (l : Level) → Precategory (lsuc l) l
Set-Precategory = precategory-Large-Precategory Set-Large-Precategory
```

### The category of small sets

The precategory of sets and functions in a given universe is a category.

```agda
Set-Category : (l : Level) → Category (lsuc l) l
Set-Category = category-Large-Category Set-Large-Category

is-category-Set-Precategory :
  (l : Level) → is-category-Precategory (Set-Precategory l)
is-category-Set-Precategory l =
  is-category-Category (Set-Category l)
```

## Properties

### The precategory of small sets is complete

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (F : functor-Precategory C (Set-Precategory (l1 ⊔ l2)))
  where

  type-vertex-limit-Set-Precategory : UU (l1 ⊔ l2)
  type-vertex-limit-Set-Precategory =
    natural-transformation-Precategory C (Set-Precategory (l1 ⊔ l2))
      ( constant-functor-Precategory C (Set-Precategory (l1 ⊔ l2))
        ( raise-unit-Set (l1 ⊔ l2)))
      ( F)

  is-set-vertex-limit-Set-Precategory :
    is-set type-vertex-limit-Set-Precategory
  is-set-vertex-limit-Set-Precategory =
    is-set-natural-transformation-Precategory C (Set-Precategory (l1 ⊔ l2))
      ( constant-functor-Precategory C (Set-Precategory (l1 ⊔ l2))
        ( raise-unit-Set (l1 ⊔ l2)))
      ( F)

  vertex-limit-Set-Precategory : Set (l1 ⊔ l2)
  vertex-limit-Set-Precategory =
    natural-transformation-set-Precategory C (Set-Precategory (l1 ⊔ l2))
      ( constant-functor-Precategory C (Set-Precategory (l1 ⊔ l2))
        ( raise-unit-Set (l1 ⊔ l2)))
      ( F)

  component-limit-Set-Precategory :
    (x : obj-Precategory C) →
    hom-Precategory (Set-Precategory (l1 ⊔ l2))
      ( vertex-limit-Set-Precategory)
      ( obj-functor-Precategory C (Set-Precategory (l1 ⊔ l2)) F x)
  component-limit-Set-Precategory c τ =
    hom-family-natural-transformation-Precategory C (Set-Precategory (l1 ⊔ l2))
      ( constant-functor-Precategory C (Set-Precategory (l1 ⊔ l2))
        ( raise-unit-Set (l1 ⊔ l2)))
      ( F)
      ( τ)
      ( c)
      ( raise-star)

  extension-limit-Set-Precategory :
    functor-Precategory terminal-Precategory (Set-Precategory (l1 ⊔ l2))
  extension-limit-Set-Precategory =
    constant-functor-Precategory
      ( terminal-Precategory)
      ( Set-Precategory (l1 ⊔ l2))
      ( vertex-limit-Set-Precategory)

  right-extension-limit-Set-Precategory :
    right-extension-Precategory
      ( C)
      ( terminal-Precategory)
      ( Set-Precategory (l1 ⊔ l2))
      ( terminal-functor-Precategory C)
      ( F)
  pr1 right-extension-limit-Set-Precategory =
    extension-limit-Set-Precategory
  pr1 (pr2 right-extension-limit-Set-Precategory) =
    component-limit-Set-Precategory
  pr2 (pr2 right-extension-limit-Set-Precategory) f =
    eq-htpy
      ( λ τ →
        ( htpy-eq
          ( naturality-natural-transformation-Precategory
            ( C)
            ( Set-Precategory (l1 ⊔ l2))
            ( constant-functor-Precategory C (Set-Precategory (l1 ⊔ l2))
              ( raise-unit-Set (l1 ⊔ l2)))
            ( F)
            ( τ)
            ( f))
          ( raise-star)))

  vertex-limit-Set-Precategory-right-extension-Precategory :
    ( φ : right-extension-Precategory C terminal-Precategory
      ( Set-Precategory (l1 ⊔ l2)) (terminal-functor-Precategory C) F) →
    hom-Precategory
      ( Set-Precategory (l1 ⊔ l2))
      ( vertex-right-extension-Precategory C (Set-Precategory (l1 ⊔ l2)) F φ)
      ( vertex-limit-Set-Precategory)
  pr1 (vertex-limit-Set-Precategory-right-extension-Precategory φ l)
    x (map-raise star) =
      hom-family-right-extension-Precategory C terminal-Precategory
        ( Set-Precategory (l1 ⊔ l2)) (terminal-functor-Precategory C) F φ x l
  pr2 (vertex-limit-Set-Precategory-right-extension-Precategory φ l) {x} {y} f =
    eq-htpy
      λ { (map-raise star) →
        ( htpy-eq
          ( naturality-right-extension-Precategory C terminal-Precategory
            ( Set-Precategory (l1 ⊔ l2))
            ( terminal-functor-Precategory C) F φ f) l) ∙
          ap
            ( hom-family-right-extension-Precategory C terminal-Precategory
              ( Set-Precategory (l1 ⊔ l2))
              ( terminal-functor-Precategory C) F φ y)
            ( htpy-eq
              ( preserves-id-functor-Precategory
                ( terminal-Precategory)
                ( Set-Precategory (l1 ⊔ l2))
                ( extension-right-extension-Precategory C terminal-Precategory
                  ( Set-Precategory (l1 ⊔ l2))
                  ( terminal-functor-Precategory C) F φ)
                ( star))
              ( l))}

  map-inv-right-extension-map-limit-Set-Precategory :
    ( G :
      functor-Precategory
        ( terminal-Precategory)
        (Set-Precategory (l1 ⊔ l2))) →
    natural-transformation-Precategory C
      ( Set-Precategory (l1 ⊔ l2))
      ( comp-functor-Precategory C terminal-Precategory
        ( Set-Precategory (l1 ⊔ l2))
        ( G)
        ( terminal-functor-Precategory C))
      ( F) →
    natural-transformation-Precategory
      ( terminal-Precategory)
      ( Set-Precategory (l1 ⊔ l2))
      ( G)
      ( extension-limit-Set-Precategory)
  pr1 (map-inv-right-extension-map-limit-Set-Precategory G φ) x =
    vertex-limit-Set-Precategory-right-extension-Precategory (G , φ)
  pr2 (map-inv-right-extension-map-limit-Set-Precategory G φ)
    {star} {star} star =
    eq-htpy
      λ x →
        ap
          ( vertex-limit-Set-Precategory-right-extension-Precategory (G , φ))
          ( inv
            ( htpy-eq
              ( preserves-id-functor-Precategory
                ( terminal-Precategory)
                ( Set-Precategory (l1 ⊔ l2))
                ( G)
                ( star))
              ( x)))

  is-section-right-extension-map-limit-Set-Precategory :
    ( G :
      functor-Precategory
        ( terminal-Precategory)
        (Set-Precategory (l1 ⊔ l2))) →
    is-section
      ( right-extension-map-Precategory
        ( C)
        ( terminal-Precategory)
        ( Set-Precategory (l1 ⊔ l2))
        ( terminal-functor-Precategory C)
        ( F)
        ( right-extension-limit-Set-Precategory)
        ( G))
      ( map-inv-right-extension-map-limit-Set-Precategory G)
  is-section-right-extension-map-limit-Set-Precategory G φ =
    eq-htpy-hom-family-natural-transformation-Precategory
      C
      ( Set-Precategory (l1 ⊔ l2))
      ( comp-functor-Precategory C terminal-Precategory
        ( Set-Precategory (l1 ⊔ l2))
        ( G)
        ( terminal-functor-Precategory C))
      ( F)
      ( _)
      ( φ)
      ( λ c → eq-htpy λ x → refl)

  is-retraction-right-extension-map-limit-Set-Precategory :
    ( G :
      functor-Precategory
        ( terminal-Precategory)
        (Set-Precategory (l1 ⊔ l2))) →
    is-retraction
      ( right-extension-map-Precategory
        ( C)
        ( terminal-Precategory)
        ( Set-Precategory (l1 ⊔ l2))
        ( terminal-functor-Precategory C)
        ( F)
        ( right-extension-limit-Set-Precategory)
        ( G))
      ( map-inv-right-extension-map-limit-Set-Precategory G)
  is-retraction-right-extension-map-limit-Set-Precategory G φ =
    eq-htpy-hom-family-natural-transformation-Precategory
      ( terminal-Precategory)
      ( Set-Precategory (l1 ⊔ l2))
      ( G)
      ( extension-limit-Set-Precategory)
      ( _)
      ( φ)
      ( λ {star →
        eq-htpy
          ( λ x →
            eq-htpy-hom-family-natural-transformation-Precategory
              ( C)
              ( Set-Precategory (l1 ⊔ l2))
              ( constant-functor-Precategory
                ( C)
                ( Set-Precategory (l1 ⊔ l2))
                ( raise-unit-Set (l1 ⊔ l2)))
              ( F) _ _
              ( λ z → eq-htpy (λ {(map-raise star) → refl})))})

  is-right-kan-extension-limit-Set-Precategory :
    is-right-kan-extension-Precategory
      ( C)
      ( terminal-Precategory)
      ( Set-Precategory (l1 ⊔ l2))
      ( terminal-functor-Precategory C)
      ( F)
      ( right-extension-limit-Set-Precategory)
  is-right-kan-extension-limit-Set-Precategory G =
    is-equiv-is-invertible
      ( map-inv-right-extension-map-limit-Set-Precategory G)
      ( is-section-right-extension-map-limit-Set-Precategory G)
      ( is-retraction-right-extension-map-limit-Set-Precategory G)

  limit-Set-Precategory :
    limit-Precategory C (Set-Precategory (l1 ⊔ l2)) F
  pr1 limit-Set-Precategory = right-extension-limit-Set-Precategory
  pr2 limit-Set-Precategory = is-right-kan-extension-limit-Set-Precategory

is-complete-Set-Precategory :
  (l1 l2 : Level) →
  is-complete-Precategory l1 l2 (Set-Precategory (l1 ⊔ l2))
is-complete-Set-Precategory l1 l2 C F = limit-Set-Precategory C F
```

## Comments

Since sets are equivalent to their set-truncations, the category of sets forms a
[full subprecategory](category-theory.full-large-subprecategories.md) of the
homotopy precategory of types.

## See also

- [Presheaf categories](category-theory.presheaf-categories.md)

## External links

- [Set](https://ncatlab.org/nlab/show/Set) at $n$Lab
- [Category of sets](https://en.wikipedia.org/wiki/Category_of_sets) at
  Wikipedia
