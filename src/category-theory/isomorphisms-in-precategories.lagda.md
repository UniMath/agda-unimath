# Isomorphisms in precategories

```agda
module category-theory.isomorphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An isomorphism between objects `x y : A` in a precategory `C` is a morphism
`f : hom x y` for which there exists a morphism `g : hom y x` such that

- `G ∘ F = id_x` and
- `F ∘ G = id_y`.

## Definition

### The predicate of being an isomorphism

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-iso-Precategory :
    {x y : obj-Precategory C} (f : type-hom-Precategory C x y) → UU l2
  is-iso-Precategory {x} {y} f =
    Σ ( type-hom-Precategory C y x)
      ( λ g →
        ( comp-hom-Precategory C f g ＝ id-hom-Precategory C) ×
        ( comp-hom-Precategory C g f ＝ id-hom-Precategory C))

  hom-inv-is-iso-Precategory :
    {x y : obj-Precategory C} {f : type-hom-Precategory C x y} →
    is-iso-Precategory f → type-hom-Precategory C y x
  hom-inv-is-iso-Precategory H = pr1 H

  is-section-hom-inv-is-iso-Precategory :
    {x y : obj-Precategory C} {f : type-hom-Precategory C x y}
    (H : is-iso-Precategory f) →
    comp-hom-Precategory C f (hom-inv-is-iso-Precategory H) ＝
    id-hom-Precategory C
  is-section-hom-inv-is-iso-Precategory H = pr1 (pr2 H)

  is-retraction-hom-inv-is-iso-Precategory :
    {x y : obj-Precategory C} {f : type-hom-Precategory C x y}
    (H : is-iso-Precategory f) →
    comp-hom-Precategory C (hom-inv-is-iso-Precategory H) f ＝
    id-hom-Precategory C
  is-retraction-hom-inv-is-iso-Precategory H = pr2 (pr2 H)

  abstract
    is-proof-irrelevant-is-iso-Precategory :
      {x y : obj-Precategory C} (f : type-hom-Precategory C x y) →
      is-proof-irrelevant (is-iso-Precategory f)
    pr1 (is-proof-irrelevant-is-iso-Precategory f H) = H
    pr2
      ( is-proof-irrelevant-is-iso-Precategory {x} {y} f (g , p , q))
      ( g' , p' , q') =
      eq-type-subtype
        ( λ h →
          prod-Prop
            ( Id-Prop
              ( hom-Precategory C y y)
              ( comp-hom-Precategory C f h)
              ( id-hom-Precategory C))
            ( Id-Prop
              ( hom-Precategory C x x)
              ( comp-hom-Precategory C h f)
              ( id-hom-Precategory C)))
        ( ( inv (right-unit-law-comp-hom-Precategory C g)) ∙
          ( ( ap (comp-hom-Precategory C g) (inv p')) ∙
            ( ( inv (associative-comp-hom-Precategory C g f g')) ∙
              ( ( ap (comp-hom-Precategory' C g') q) ∙
                ( left-unit-law-comp-hom-Precategory C g')))))

    is-prop-is-iso-Precategory :
      {x y : obj-Precategory C} (f : type-hom-Precategory C x y) →
      is-prop (is-iso-Precategory f)
    is-prop-is-iso-Precategory f =
      is-prop-is-proof-irrelevant (is-proof-irrelevant-is-iso-Precategory f)

  is-iso-Precategory-Prop :
    {x y : obj-Precategory C} (f : type-hom-Precategory C x y) → Prop l2
  pr1 (is-iso-Precategory-Prop f) = is-iso-Precategory f
  pr2 (is-iso-Precategory-Prop f) = is-prop-is-iso-Precategory f
```

### The type of isomorphisms between two objects

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  iso-Precategory : (x y : obj-Precategory C) → UU l2
  iso-Precategory x y = type-subtype (is-iso-Precategory-Prop C {x} {y})

  hom-iso-Precategory :
    {x y : obj-Precategory C} →
    iso-Precategory x y → type-hom-Precategory C x y
  hom-iso-Precategory f = inclusion-subtype (is-iso-Precategory-Prop C) f

  is-iso-hom-iso-Precategory :
    {x y : obj-Precategory C} (f : iso-Precategory x y) →
    is-iso-Precategory C (hom-iso-Precategory f)
  is-iso-hom-iso-Precategory f =
    is-in-subtype-inclusion-subtype (is-iso-Precategory-Prop C) f

  hom-inv-iso-Precategory :
    {x y : obj-Precategory C} →
    iso-Precategory x y → type-hom-Precategory C y x
  hom-inv-iso-Precategory f = pr1 (is-iso-hom-iso-Precategory f)

  is-section-hom-inv-iso-Precategory :
    {x y : obj-Precategory C} (f : iso-Precategory x y) →
    ( comp-hom-Precategory C
      ( hom-iso-Precategory f)
      ( hom-inv-iso-Precategory f)) ＝
    ( id-hom-Precategory C)
  is-section-hom-inv-iso-Precategory f =
    pr1 (pr2 (is-iso-hom-iso-Precategory f))

  is-retraction-hom-inv-iso-Precategory :
    {x y : obj-Precategory C} (f : iso-Precategory x y) →
    ( comp-hom-Precategory C
      ( hom-inv-iso-Precategory f)
      ( hom-iso-Precategory f)) ＝
    ( id-hom-Precategory C)
  is-retraction-hom-inv-iso-Precategory f =
    pr2 (pr2 (is-iso-hom-iso-Precategory f))

  inv-iso-Precategory :
    {x y : obj-Precategory C} → iso-Precategory x y → iso-Precategory y x
  pr1 (inv-iso-Precategory f) = hom-inv-iso-Precategory f
  pr1 (pr2 (inv-iso-Precategory f)) = hom-iso-Precategory f
  pr1 (pr2 (pr2 (inv-iso-Precategory f))) =
    is-retraction-hom-inv-iso-Precategory f
  pr2 (pr2 (pr2 (inv-iso-Precategory f))) = is-section-hom-inv-iso-Precategory f
```

## Examples

### The identity morphisms are isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = id_x` (it is its own inverse).

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-iso-id-hom-Precategory :
    {x : obj-Precategory C} → is-iso-Precategory C (id-hom-Precategory C {x})
  pr1 is-iso-id-hom-Precategory = id-hom-Precategory C
  pr1 (pr2 is-iso-id-hom-Precategory) =
    left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)
  pr2 (pr2 is-iso-id-hom-Precategory) =
    left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)

  id-iso-Precategory : {x : obj-Precategory C} → iso-Precategory C x x
  pr1 id-iso-Precategory = id-hom-Precategory C
  pr2 id-iso-Precategory = is-iso-id-hom-Precategory
```

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because by the J-rule, it is enough to construct an isomorphism given
`refl : Id x x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
iso-eq-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) →
  (x y : obj-Precategory C) → x ＝ y → iso-Precategory C x y
iso-eq-Precategory C x .x refl = id-iso-Precategory C
```

## Properties

### The property of being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to
`f`. It is enough to show that `g = g'` since the equalities are propositions
(since the hom-types are sets). But we have the following chain of equalities:
`g = g ∘ id_y = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = id_x ∘ g' = g'.`

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-set-iso-Precategory :
    (x y : obj-Precategory C) → is-set (iso-Precategory C x y)
  is-set-iso-Precategory x y =
    is-set-type-subtype
      ( is-iso-Precategory-Prop C)
      ( is-set-type-hom-Precategory C x y)

  iso-Precategory-Set : (x y : obj-Precategory C) → Set l2
  pr1 (iso-Precategory-Set x y) = iso-Precategory C x y
  pr2 (iso-Precategory-Set x y) = is-set-iso-Precategory x y
```

### When `hom x y` is a proposition, The type of isomorphisms from `x` to `y` form a proposition

The type of isomorphisms between objects `x y : A` is a subtype of `hom x y`, so
when this type is a proposition, then the type of isomorphisms from `x` to `y`
form a proposition.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y : obj-Precategory C)
  where

  is-prop-iso-Precategory :
    (is-prop-hom-C-x-y : is-prop (type-hom-Precategory C x y)) →
    is-prop (iso-Precategory C x y)
  is-prop-iso-Precategory = is-prop-type-subtype (is-iso-Precategory-Prop C)

  iso-Precategory-Prop :
    (is-prop-hom-C-x-y : is-prop (type-hom-Precategory C x y)) →
    Prop l2
  pr1 (iso-Precategory-Prop _) = iso-Precategory C x y
  pr2 (iso-Precategory-Prop is-prop-hom-C-x-y) =
    is-prop-iso-Precategory is-prop-hom-C-x-y
```

### A morphism is an isomorphism if and only if precomposition by it is an equivalence

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {x y : obj-Precategory C}
  (f : type-hom-Precategory C x y)
  where

  precomp-hom-inv-is-iso-Precategory :
    (H : is-iso-Precategory C f) (z : obj-Precategory C) →
    type-hom-Precategory C x z → type-hom-Precategory C y z
  precomp-hom-inv-is-iso-Precategory H z =
    precomp-hom-Precategory C (hom-inv-is-iso-Precategory C H) z

  is-section-precomp-hom-inv-is-iso-Precategory :
    (H : is-iso-Precategory C f) (z : obj-Precategory C) →
    ( precomp-hom-Precategory C f z ∘ precomp-hom-inv-is-iso-Precategory H z) ~
    ( id)
  is-section-precomp-hom-inv-is-iso-Precategory H z g =
    equational-reasoning
      comp-hom-Precategory
        ( C)
        ( comp-hom-Precategory C g (hom-inv-is-iso-Precategory C H))
        ( f)
      ＝ comp-hom-Precategory
          ( C)
          ( g)
          ( comp-hom-Precategory C (hom-inv-is-iso-Precategory C H) f)
        by
        associative-comp-hom-Precategory C g (hom-inv-is-iso-Precategory C H) f
      ＝ comp-hom-Precategory C g (id-hom-Precategory C)
        by
        ap
          ( comp-hom-Precategory C g)
          ( is-retraction-hom-inv-is-iso-Precategory C H)
      ＝ g
        by right-unit-law-comp-hom-Precategory C g

  is-retraction-precomp-hom-inv-is-iso-Precategory :
    (H : is-iso-Precategory C f) (z : obj-Precategory C) →
    ( precomp-hom-inv-is-iso-Precategory H z ∘ precomp-hom-Precategory C f z) ~
    ( id)
  is-retraction-precomp-hom-inv-is-iso-Precategory H z g =
    equational-reasoning
      comp-hom-Precategory
        ( C)
        ( comp-hom-Precategory C g f)
        ( hom-inv-is-iso-Precategory C H)
      ＝ comp-hom-Precategory
          ( C)
          ( g)
          ( comp-hom-Precategory C f (hom-inv-is-iso-Precategory C H))
        by
        associative-comp-hom-Precategory C g f (hom-inv-is-iso-Precategory C H)
      ＝ comp-hom-Precategory C g (id-hom-Precategory C)
        by
        ap
          ( comp-hom-Precategory C g)
          ( is-section-hom-inv-is-iso-Precategory C H)
      ＝ g
        by right-unit-law-comp-hom-Precategory C g

  is-equiv-precomp-is-iso-Precategory :
    (H : is-iso-Precategory C f) (z : obj-Precategory C) →
    is-equiv (precomp-hom-Precategory C f z)
  is-equiv-precomp-is-iso-Precategory H z =
    is-equiv-is-invertible
      ( precomp-hom-inv-is-iso-Precategory H z)
      ( is-section-precomp-hom-inv-is-iso-Precategory H z)
      ( is-retraction-precomp-hom-inv-is-iso-Precategory H z)
```

### When `hom x y` and `hom y x` are propositions, it suffices to provide a homomorphism in each direction to construct an isomorphism

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (x y : obj-Precategory C)
  where

  is-iso-is-prop-hom-Precategory' :
    is-prop (type-hom-Precategory C x x) →
    is-prop (type-hom-Precategory C y y) →
    (f : type-hom-Precategory C x y) →
    type-hom-Precategory C y x →
    is-iso-Precategory C f
  pr1 (is-iso-is-prop-hom-Precategory' _ _ f g) = g
  pr1 (pr2 (is-iso-is-prop-hom-Precategory' _ is-prop-hom-C-y-y f g)) =
    eq-is-prop is-prop-hom-C-y-y
  pr2 (pr2 (is-iso-is-prop-hom-Precategory' is-prop-hom-C-x-x _ f g)) =
    eq-is-prop is-prop-hom-C-x-x

  iso-is-prop-hom-Precategory' :
    is-prop (type-hom-Precategory C x x) →
    is-prop (type-hom-Precategory C y y) →
    type-hom-Precategory C x y →
    type-hom-Precategory C y x →
    iso-Precategory C x y
  pr1 (iso-is-prop-hom-Precategory' _ _ f g) = f
  pr2 (iso-is-prop-hom-Precategory' is-prop-hom-C-x-x is-prop-hom-C-y-y f g) =
    is-iso-is-prop-hom-Precategory' is-prop-hom-C-x-x is-prop-hom-C-y-y f g

  is-iso-is-prop-hom-Precategory :
    (( x' y' : obj-Precategory C) → is-prop (type-hom-Precategory C x' y')) →
    (f : type-hom-Precategory C x y) → type-hom-Precategory C y x →
    is-iso-Precategory C f
  is-iso-is-prop-hom-Precategory is-prop-hom-C =
    is-iso-is-prop-hom-Precategory' (is-prop-hom-C x x) (is-prop-hom-C y y)

  iso-is-prop-hom-Precategory :
    (( x' y' : obj-Precategory C) → is-prop (type-hom-Precategory C x' y')) →
    type-hom-Precategory C x y →
    type-hom-Precategory C y x →
    iso-Precategory C x y
  iso-is-prop-hom-Precategory is-prop-hom-C =
    iso-is-prop-hom-Precategory' (is-prop-hom-C x x) (is-prop-hom-C y y)
```
