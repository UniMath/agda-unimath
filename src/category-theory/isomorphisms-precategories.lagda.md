# Isomorphisms in precategories

```agda
module category-theory.isomorphisms-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An isomorphism between objects `x y : A` in a precategory `C` is a morphism `f : hom x y` for which there exists a morphism `g : hom y x` such that
- `comp g f = id_x` and
- `comp f g = id_y`.

## Definition

### The property of being an isomorphism

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-iso-Precat : {x y : obj-Precat C} (f : type-hom-Precat C x y) → UU l2
  is-iso-Precat {x} {y} f =
    Σ ( type-hom-Precat C y x)
      ( λ g →
        (comp-hom-Precat C f g ＝ id-hom-Precat C) ×
        (comp-hom-Precat C g f ＝ id-hom-Precat C))

  hom-inv-is-iso-Precat :
    {x y : obj-Precat C} {f : type-hom-Precat C x y} →
    is-iso-Precat f → type-hom-Precat C y x
  hom-inv-is-iso-Precat H = pr1 H

  issec-hom-inv-is-iso-Precat :
    {x y : obj-Precat C} {f : type-hom-Precat C x y} (H : is-iso-Precat f) →
    (comp-hom-Precat C f (hom-inv-is-iso-Precat H)) ＝ id-hom-Precat C
  issec-hom-inv-is-iso-Precat H = pr1 (pr2 H)

  isretr-hom-inv-is-iso-Precat :
    {x y : obj-Precat C} {f : type-hom-Precat C x y} (H : is-iso-Precat f) →
    (comp-hom-Precat C (hom-inv-is-iso-Precat H) f) ＝ id-hom-Precat C
  isretr-hom-inv-is-iso-Precat H = pr2 (pr2 H)

  abstract
    is-proof-irrelevant-is-iso-Precat :
      {x y : obj-Precat C} (f : type-hom-Precat C x y) →
      is-proof-irrelevant (is-iso-Precat f)
    pr1 (is-proof-irrelevant-is-iso-Precat f H) = H
    pr2
      ( is-proof-irrelevant-is-iso-Precat {x} {y} f
        ( pair g (pair p q)))
        ( pair g' (pair p' q')) =
      eq-type-subtype
        ( λ h →
          prod-Prop
            ( Id-Prop
              ( hom-Precat C y y)
              ( comp-hom-Precat C f h)
              ( id-hom-Precat C))
            ( Id-Prop
              ( hom-Precat C x x)
              ( comp-hom-Precat C h f)
              ( id-hom-Precat C)))
        ( ( inv (right-unit-law-comp-hom-Precat C g)) ∙
          ( ( ap (comp-hom-Precat C g) (inv p')) ∙
            ( ( inv (assoc-comp-hom-Precat C g f g')) ∙
              ( ( ap (comp-hom-Precat' C g') q) ∙
                ( left-unit-law-comp-hom-Precat C g')))))

    is-prop-is-iso-Precat :
      {x y : obj-Precat C} (f : type-hom-Precat C x y) →
      is-prop (is-iso-Precat f)
    is-prop-is-iso-Precat f =
      is-prop-is-proof-irrelevant (is-proof-irrelevant-is-iso-Precat f)

  is-iso-precat-Prop :
    {x y : obj-Precat C} (f : type-hom-Precat C x y) → Prop l2
  pr1 (is-iso-precat-Prop f) = is-iso-Precat f
  pr2 (is-iso-precat-Prop f) = is-prop-is-iso-Precat f
```

### The type of isomorphisms between two objects in a precategory

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  iso-Precat : (x y : obj-Precat C) → UU l2
  iso-Precat x y = type-subtype (is-iso-precat-Prop C {x} {y})

  hom-iso-Precat :
    {x y : obj-Precat C} → iso-Precat x y → type-hom-Precat C x y
  hom-iso-Precat f = inclusion-subtype (is-iso-precat-Prop C) f

  is-iso-hom-iso-Precat :
    {x y : obj-Precat C} (f : iso-Precat x y) →
    is-iso-Precat C (hom-iso-Precat f)
  is-iso-hom-iso-Precat f =
    is-in-subtype-inclusion-subtype (is-iso-precat-Prop C) f

  hom-inv-iso-Precat :
    {x y : obj-Precat C} → iso-Precat x y → type-hom-Precat C y x
  hom-inv-iso-Precat f = pr1 (is-iso-hom-iso-Precat f)

  issec-hom-inv-iso-Precat :
    {x y : obj-Precat C} (f : iso-Precat x y) →
    ( comp-hom-Precat C (hom-iso-Precat f) (hom-inv-iso-Precat f)) ＝
    ( id-hom-Precat C)
  issec-hom-inv-iso-Precat f = pr1 (pr2 (is-iso-hom-iso-Precat f))

  isretr-hom-inv-iso-Precat :
    {x y : obj-Precat C} (f : iso-Precat x y) →
    ( comp-hom-Precat C (hom-inv-iso-Precat f) (hom-iso-Precat f)) ＝
    ( id-hom-Precat C)
  isretr-hom-inv-iso-Precat f = pr2 (pr2 (is-iso-hom-iso-Precat f))
```

## Examples

### The identity morphisms are isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism from `x` to `x` since `comp id_x id_x = id_x` (it is its own inverse).

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-iso-id-hom-Precat :
    {x : obj-Precat C} → is-iso-Precat C (id-hom-Precat C {x})
  pr1 is-iso-id-hom-Precat = id-hom-Precat C
  pr1 (pr2 is-iso-id-hom-Precat) =
    left-unit-law-comp-hom-Precat C (id-hom-Precat C)
  pr2 (pr2 is-iso-id-hom-Precat) =
    left-unit-law-comp-hom-Precat C (id-hom-Precat C)

  id-iso-Precat : {x : obj-Precat C} → iso-Precat C x x
  pr1 id-iso-Precat = id-hom-Precat C
  pr2 id-iso-Precat = is-iso-id-hom-Precat
```

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them. This is because by the J-rule, it is enough to construct an isomorphism given `refl : Id x x`, from `x` to itself. We take the identity morphism as such an isomorphism.

```agda
iso-eq-Precat :
  {l1 l2 : Level} (C : Precat l1 l2) →
  (x y : obj-Precat C) → x ＝ y → iso-Precat C x y
iso-eq-Precat C x .x refl = id-iso-Precat C
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

```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set `hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2)
  where

  is-set-iso-Precat : (x y : obj-Precat C) → is-set (iso-Precat C x y)
  is-set-iso-Precat x y =
    is-set-type-subtype
      ( is-iso-precat-Prop C)
      ( is-set-type-hom-Precat C x y)

  iso-Precat-Set : (x y : obj-Precat C) → Set l2
  pr1 (iso-Precat-Set x y) = iso-Precat C x y
  pr2 (iso-Precat-Set x y) = is-set-iso-Precat x y
```

### A morphism is an isomorphism if and only if precomposition by it is an equivalence

```agda
module _
  {l1 l2 : Level} (C : Precat l1 l2) {x y : obj-Precat C}
  (f : type-hom-Precat C x y)
  where

  precomp-hom-inv-is-iso-Precat :
    (H : is-iso-Precat C f) (z : obj-Precat C) →
    type-hom-Precat C x z → type-hom-Precat C y z
  precomp-hom-inv-is-iso-Precat H z =
    precomp-hom-Precat C (hom-inv-is-iso-Precat C H) z

  issec-precomp-hom-inv-is-iso-Precat :
    (H : is-iso-Precat C f) (z : obj-Precat C) →
    ( precomp-hom-Precat C f z ∘ precomp-hom-inv-is-iso-Precat H z) ~ id
  issec-precomp-hom-inv-is-iso-Precat H z g =
    equational-reasoning
      comp-hom-Precat C (comp-hom-Precat C g (hom-inv-is-iso-Precat C H)) f
      ＝ comp-hom-Precat C g (comp-hom-Precat C (hom-inv-is-iso-Precat C H) f)
        by assoc-comp-hom-Precat C g (hom-inv-is-iso-Precat C H) f
      ＝ comp-hom-Precat C g (id-hom-Precat C)
        by ap (comp-hom-Precat C g) (isretr-hom-inv-is-iso-Precat C H)
      ＝ g
        by right-unit-law-comp-hom-Precat C g

  isretr-precomp-hom-inv-is-iso-Precat :
    (H : is-iso-Precat C f) (z : obj-Precat C) →
    (precomp-hom-inv-is-iso-Precat H z ∘ precomp-hom-Precat C f z) ~ id
  isretr-precomp-hom-inv-is-iso-Precat H z g =
    equational-reasoning
      comp-hom-Precat C (comp-hom-Precat C g f) (hom-inv-is-iso-Precat C H)
      ＝ comp-hom-Precat C g (comp-hom-Precat C f (hom-inv-is-iso-Precat C H))
        by assoc-comp-hom-Precat C g f (hom-inv-is-iso-Precat C H)
      ＝ comp-hom-Precat C g (id-hom-Precat C)
        by ap (comp-hom-Precat C g) (issec-hom-inv-is-iso-Precat C H)
      ＝ g
        by right-unit-law-comp-hom-Precat C g

  is-equiv-precomp-is-iso-Precat :
    (H : is-iso-Precat C f) (z : obj-Precat C) →
    is-equiv (precomp-hom-Precat C f z)
  is-equiv-precomp-is-iso-Precat H z =
    is-equiv-has-inverse
      ( precomp-hom-inv-is-iso-Precat H z)
      ( issec-precomp-hom-inv-is-iso-Precat H z)
      ( isretr-precomp-hom-inv-is-iso-Precat H z)
```
