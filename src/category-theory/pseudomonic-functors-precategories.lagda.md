# Pseudomonic functors between precategories

```agda
module category-theory.pseudomonic-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.conservative-functors-precategories
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterated-dependent-product-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) between
[precategories](category-theory.precategories.md) `C` and `D` is
{{#concept "pseudomonic" Disambiguation="functor between precategories" Agda=is-pseudomonic-functor-Precategory}}
if it is [faithful](category-theory.faithful-functors-precategories.md) on all
morphism-[sets](foundation-core.sets.md) and full on
[isomorphisms](category-theory.isomorphisms-in-precategories.md). In particular,
this means it induces an [equivalence](foundation-core.equivalences.md) on
isomorphism-sets.

Pseudomonic functors present
[replete subprecategories](category-theory.replete-subprecategories.md), which
is the "right notion" of subcategory with respect to the _principle of
invariance under equivalences_.

## Definition

### The predicate on isomorphisms of being full

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-full-on-isos-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-full-on-isos-functor-Precategory =
    (x y : obj-Precategory C) →
    is-surjective (preserves-iso-functor-Precategory C D F {x} {y})

  is-prop-is-full-on-isos-functor-Precategory :
    is-prop is-full-on-isos-functor-Precategory
  is-prop-is-full-on-isos-functor-Precategory =
    is-prop-iterated-Π 2
      ( λ x y → is-prop-is-surjective (preserves-iso-functor-Precategory C D F))

  is-full-on-isos-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 is-full-on-isos-prop-functor-Precategory =
    is-full-on-isos-functor-Precategory
  pr2 is-full-on-isos-prop-functor-Precategory =
    is-prop-is-full-on-isos-functor-Precategory
```

### The predicate of being pseudomonic

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-pseudomonic-prop-functor-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-pseudomonic-prop-functor-Precategory =
    product-Prop
      ( is-faithful-prop-functor-Precategory C D F)
      ( is-full-on-isos-prop-functor-Precategory C D F)

  is-pseudomonic-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-pseudomonic-functor-Precategory =
    type-Prop is-pseudomonic-prop-functor-Precategory

  is-prop-is-pseudomonic-functor-Precategory :
    is-prop is-pseudomonic-functor-Precategory
  is-prop-is-pseudomonic-functor-Precategory =
    is-prop-type-Prop is-pseudomonic-prop-functor-Precategory

  is-faithful-is-pseudomonic-functor-Precategory :
    is-pseudomonic-functor-Precategory →
    is-faithful-functor-Precategory C D F
  is-faithful-is-pseudomonic-functor-Precategory = pr1

  is-full-on-isos-is-pseudomonic-functor-Precategory :
    is-pseudomonic-functor-Precategory →
    is-full-on-isos-functor-Precategory C D F
  is-full-on-isos-is-pseudomonic-functor-Precategory = pr2
```

### The type of pseudomonic functors between two precategories

```agda
pseudomonic-functor-Precategory :
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
pseudomonic-functor-Precategory C D =
  Σ (functor-Precategory C D) (is-pseudomonic-functor-Precategory C D)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : pseudomonic-functor-Precategory C D)
  where

  functor-pseudomonic-functor-Precategory : functor-Precategory C D
  functor-pseudomonic-functor-Precategory = pr1 F

  is-pseudomonic-pseudomonic-functor-Precategory :
    is-pseudomonic-functor-Precategory C D
      functor-pseudomonic-functor-Precategory
  is-pseudomonic-pseudomonic-functor-Precategory = pr2 F

  obj-pseudomonic-functor-Precategory : obj-Precategory C → obj-Precategory D
  obj-pseudomonic-functor-Precategory =
    obj-functor-Precategory C D functor-pseudomonic-functor-Precategory

  hom-pseudomonic-functor-Precategory :
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-pseudomonic-functor-Precategory x)
      ( obj-pseudomonic-functor-Precategory y)
  hom-pseudomonic-functor-Precategory =
    hom-functor-Precategory C D functor-pseudomonic-functor-Precategory

  is-faithful-pseudomonic-functor-Precategory :
    is-faithful-functor-Precategory C D functor-pseudomonic-functor-Precategory
  is-faithful-pseudomonic-functor-Precategory =
    is-faithful-is-pseudomonic-functor-Precategory C D
      functor-pseudomonic-functor-Precategory
      is-pseudomonic-pseudomonic-functor-Precategory

  is-full-on-isos-pseudomonic-functor-Precategory :
    is-full-on-isos-functor-Precategory C D
      functor-pseudomonic-functor-Precategory
  is-full-on-isos-pseudomonic-functor-Precategory =
    is-full-on-isos-is-pseudomonic-functor-Precategory C D
      functor-pseudomonic-functor-Precategory
      is-pseudomonic-pseudomonic-functor-Precategory
```

## Properties

### Pseudomonic functors are equivalences on isomorphism-sets

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (is-pseudomonic-F : is-pseudomonic-functor-Precategory C D F)
  {x y : obj-Precategory C}
  where

  is-equiv-preserves-iso-is-pseudomonic-functor-Precategory :
    is-equiv (preserves-iso-functor-Precategory C D F {x} {y})
  is-equiv-preserves-iso-is-pseudomonic-functor-Precategory =
    is-equiv-is-emb-is-surjective
      ( pr2 is-pseudomonic-F x y)
      ( is-faithful-on-isos-is-faithful-functor-Precategory
          C D F (pr1 is-pseudomonic-F) x y)

  equiv-iso-is-pseudomonic-functor-Precategory :
    iso-Precategory C x y ≃
    iso-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y)
  pr1 equiv-iso-is-pseudomonic-functor-Precategory =
    preserves-iso-functor-Precategory C D F
  pr2 equiv-iso-is-pseudomonic-functor-Precategory =
    is-equiv-preserves-iso-is-pseudomonic-functor-Precategory

  inv-equiv-iso-is-pseudomonic-functor-Precategory :
    iso-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y) ≃
    iso-Precategory C x y
  inv-equiv-iso-is-pseudomonic-functor-Precategory =
    inv-equiv equiv-iso-is-pseudomonic-functor-Precategory

  map-inv-iso-is-pseudomonic-functor-Precategory :
    iso-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y) →
    iso-Precategory C x y
  map-inv-iso-is-pseudomonic-functor-Precategory =
    map-equiv inv-equiv-iso-is-pseudomonic-functor-Precategory
```

The previous entry records what is also known as "essential injectivity".

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : pseudomonic-functor-Precategory C D)
  {x y : obj-Precategory C}
  where

  equiv-iso-pseudomonic-functor-Precategory :
    iso-Precategory C x y ≃
    iso-Precategory D
      ( obj-pseudomonic-functor-Precategory C D F x)
      ( obj-pseudomonic-functor-Precategory C D F y)
  equiv-iso-pseudomonic-functor-Precategory =
    equiv-iso-is-pseudomonic-functor-Precategory C D
      ( functor-pseudomonic-functor-Precategory C D F)
      ( is-pseudomonic-pseudomonic-functor-Precategory C D F)

  inv-equiv-iso-pseudomonic-functor-Precategory :
    iso-Precategory D
      ( obj-pseudomonic-functor-Precategory C D F x)
      ( obj-pseudomonic-functor-Precategory C D F y) ≃
    iso-Precategory C x y
  inv-equiv-iso-pseudomonic-functor-Precategory =
    inv-equiv equiv-iso-pseudomonic-functor-Precategory

  map-inv-hom-pseudomonic-functor-Precategory :
    iso-Precategory D
      ( obj-pseudomonic-functor-Precategory C D F x)
      ( obj-pseudomonic-functor-Precategory C D F y) →
    iso-Precategory C x y
  map-inv-hom-pseudomonic-functor-Precategory =
    map-equiv inv-equiv-iso-pseudomonic-functor-Precategory
```

The previous entry records what is also known as "essential injectivity".

### Pseudomonic functors are conservative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (is-pseudomonic-F : is-pseudomonic-functor-Precategory C D F)
  {x y : obj-Precategory C}
  where

  is-conservative-is-pseudomonic-functor-Precategory :
    is-conservative-functor-Precategory C D F
  is-conservative-is-pseudomonic-functor-Precategory f is-iso-Ff =
    ind-trunc-Prop
      ( λ _ → is-iso-prop-Precategory C f)
      ( λ ((e , e' , l , r) , p) →
        ( e' ,
          ( inv
            ( ap
              ( λ g → comp-hom-Precategory C g e')
              ( is-injective-is-emb
                ( is-faithful-is-pseudomonic-functor-Precategory
                    ( C) D F is-pseudomonic-F _ _)
                ( ap pr1 p)))) ∙
          ( l) ,
          ( inv
            ( ap
              ( comp-hom-Precategory C e')
              ( is-injective-is-emb
                ( is-faithful-is-pseudomonic-functor-Precategory
                    ( C) D F is-pseudomonic-F _ _)
                ( ap pr1 p)))) ∙
          ( r)))
      ( pr2 is-pseudomonic-F _ _ (hom-functor-Precategory C D F f , is-iso-Ff))
```

## See also

- Pseudomonic functors present
  [replete subprecategories](category-theory.replete-subprecategories.md).
- [Fully faithful functors between precategories](category-theory.fully-faithful-functors-precategories.md)

## External links

- [Pseudomonic Functors](https://1lab.dev/Cat.Functor.Properties.html#pseudomonic-functors)
  at 1lab
- [pseudomonic functor](https://ncatlab.org/nlab/show/pseudomonic+functor) at
  $n$Lab

A wikidata identifier was not available for this concept.
