# Isomorphisms in precategories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.isomorphisms-precategories where

open import categories.precategories using
  ( Precat; obj-Precat; type-hom-Precat; comp-Precat;
    id-Precat; hom-Precat; right-unit-law-comp-Precat;
    left-unit-law-comp-Precat; assoc-comp-Precat; comp-Precat';
    is-set-type-hom-Precat)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; inv; _∙_; ap)
open import foundation.propositions using
  ( is-proof-irrelevant; prod-Prop; is-prop;
    is-prop-is-proof-irrelevant)
open import foundation.sets using (Id-Prop; is-set; UU-Set)
open import foundation.subtypes using (eq-subtype; is-set-is-subtype)
open import foundation.universe-levels using (UU; Level)
```

## Idea

An isomorphism between objects `x y : A` in a precategory `C` is a morphism `f : hom x y` for which there exists a morphism `g : hom y x` such that
- `comp g f = id_x` and
- `comp f g = id_y`.

## Definition

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-iso-Precat : {x y : obj-Precat C} (f : type-hom-Precat C x y) → UU l2
  is-iso-Precat {x} {y} f =
    Σ ( type-hom-Precat C y x)
       ( λ g → Id (comp-Precat C f g) (id-Precat C) ×
               Id (comp-Precat C g f) (id-Precat C))

  iso-Precat : (x y : obj-Precat C) → UU l2
  iso-Precat x y = Σ (type-hom-Precat C x y) is-iso-Precat
```

## Examples

### The identity morphisms are isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism from `x` to `x` since `comp id_x id_x = id_x` (it is its own inverse).

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-iso-id-Precat : {x : obj-Precat C} → is-iso-Precat C (id-Precat C {x})
  pr1 is-iso-id-Precat = id-Precat C
  pr1 (pr2 is-iso-id-Precat) = left-unit-law-comp-Precat C (id-Precat C)
  pr2 (pr2 is-iso-id-Precat) = left-unit-law-comp-Precat C (id-Precat C)

  id-iso-Precat : {x : obj-Precat C} → iso-Precat C x x
  pr1 id-iso-Precat = id-Precat C
  pr2 id-iso-Precat = is-iso-id-Precat
```

## Properties

### The property of being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to `f`. It is enough to show that `g = g'` since the equalities are propositions (since the hom-types are sets). But we have the following chain of equalities:
`g = comp g id_y
   = comp g (comp f g')
   = comp (comp g f) g'
   = comp id_x g'
   = g'.`

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  abstract
    is-proof-irrelevant-is-iso-Precat :
      {x y : obj-Precat C} (f : type-hom-Precat C x y) →
      is-proof-irrelevant (is-iso-Precat C f)
    pr1 (is-proof-irrelevant-is-iso-Precat f H) = H
    pr2
      ( is-proof-irrelevant-is-iso-Precat {x} {y} f
        ( pair g (pair p q)))
        ( pair g' (pair p' q')) =
      eq-subtype
        ( λ h →
          prod-Prop
            ( Id-Prop (hom-Precat C y y) (comp-Precat C f h) (id-Precat C))
            ( Id-Prop (hom-Precat C x x) (comp-Precat C h f) (id-Precat C)))
        ( ( inv (right-unit-law-comp-Precat C g)) ∙
          ( ( ap (comp-Precat C g) (inv p')) ∙
            ( ( inv (assoc-comp-Precat C g f g')) ∙
              ( ( ap (comp-Precat' C g') q) ∙
                ( left-unit-law-comp-Precat C g')))))

    is-prop-is-iso-Precat :
      {x y : obj-Precat C} (f : type-hom-Precat C x y) →
      is-prop (is-iso-Precat C f)
    is-prop-is-iso-Precat f =
      is-prop-is-proof-irrelevant (is-proof-irrelevant-is-iso-Precat f)

  is-set-iso-Precat : (x y : obj-Precat C) → is-set (iso-Precat C x y)
  is-set-iso-Precat x y =
    is-set-is-subtype
      is-prop-is-iso-Precat
      (is-set-type-hom-Precat C x y)

  iso-Precat-Set : (x y : obj-Precat C) → UU-Set l2
  pr1 (iso-Precat-Set x y) = iso-Precat C x y
  pr2 (iso-Precat-Set x y) = is-set-iso-Precat x y
```
