# Precategories

```agda
module category-theory.precategories where

open import category-theory.nonunital-precategories public
```

<details><summary>Imports</summary>

```agda
open import category-theory.nonunital-precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A **precategory** in Homotopy Type Theory consists of:

- a type `A` of objects,
- for each pair of objects `x y : A`, a [set](foundation-core.sets.md) of
  morphisms `hom x y : Set`, together with a composition operation
  `_∘_ : hom y z → hom x y → hom x z` such that:
- `(h ∘ g) ∘ f = h ∘ (g ∘ f)` for any morphisms `h : hom z w`, `g : hom y z` and
  `f : hom x y`,
- for each object `x : A` there is a morphism `id_x : hom x x` such that
  `id_x ∘ f = f` and `g ∘ id_x = g` for any morphisms `f : hom x y` and
  `g : hom z x`.

The reason this is called a *pre*category and not a category in Homotopy Type
Theory is that we want to reserve that name for precategories where the
identities between the objects are exactly the isomorphisms.

## Definition

```agda
Precategory :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precategory l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → Set l2)
        ( λ hom →
          Σ ( associative-composition-structure-Set hom)
            ( λ μ → is-unital-composition-operation-Set hom (pr1 μ))))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  obj-Precategory : UU l1
  obj-Precategory = pr1 C

  hom-set-Precategory : (x y : obj-Precategory) → Set l2
  hom-set-Precategory = pr1 (pr2 C)

  hom-Precategory : (x y : obj-Precategory) → UU l2
  hom-Precategory x y = type-Set (hom-set-Precategory x y)

  is-set-hom-Precategory :
    (x y : obj-Precategory) → is-set (hom-Precategory x y)
  is-set-hom-Precategory x y = is-set-type-Set (hom-set-Precategory x y)

  associative-composition-structure-Precategory :
    associative-composition-structure-Set hom-set-Precategory
  associative-composition-structure-Precategory = pr1 (pr2 (pr2 C))

  comp-hom-Precategory :
    {x y z : obj-Precategory} →
    hom-Precategory y z →
    hom-Precategory x y →
    hom-Precategory x z
  comp-hom-Precategory = pr1 associative-composition-structure-Precategory

  comp-hom-Precategory' :
    {x y z : obj-Precategory} →
    hom-Precategory x y →
    hom-Precategory y z →
    hom-Precategory x z
  comp-hom-Precategory' f g = comp-hom-Precategory g f

  associative-comp-hom-Precategory :
    {x y z w : obj-Precategory}
    (h : hom-Precategory z w)
    (g : hom-Precategory y z)
    (f : hom-Precategory x y) →
    ( comp-hom-Precategory (comp-hom-Precategory h g) f) ＝
    ( comp-hom-Precategory h (comp-hom-Precategory g f))
  associative-comp-hom-Precategory =
    pr2 associative-composition-structure-Precategory

  is-unital-composition-operation-Precategory :
    is-unital-composition-operation-Set
      hom-set-Precategory
      comp-hom-Precategory
  is-unital-composition-operation-Precategory = pr2 (pr2 (pr2 C))

  id-hom-Precategory : {x : obj-Precategory} → hom-Precategory x x
  id-hom-Precategory {x} = pr1 is-unital-composition-operation-Precategory x

  left-unit-law-comp-hom-Precategory :
    {x y : obj-Precategory} (f : hom-Precategory x y) →
    comp-hom-Precategory id-hom-Precategory f ＝ f
  left-unit-law-comp-hom-Precategory =
    pr1 (pr2 is-unital-composition-operation-Precategory)

  right-unit-law-comp-hom-Precategory :
    {x y : obj-Precategory} (f : hom-Precategory x y) →
    comp-hom-Precategory f id-hom-Precategory ＝ f
  right-unit-law-comp-hom-Precategory =
    pr2 (pr2 is-unital-composition-operation-Precategory)
```

### The underlying nonunital precategory of a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  nonunital-precategory-Precategory : Nonunital-Precategory l1 l2
  pr1 nonunital-precategory-Precategory = obj-Precategory C
  pr1 (pr2 nonunital-precategory-Precategory) = hom-set-Precategory C
  pr1 (pr2 (pr2 nonunital-precategory-Precategory)) = comp-hom-Precategory C
  pr2 (pr2 (pr2 nonunital-precategory-Precategory)) =
    associative-comp-hom-Precategory C
```

### The total hom-type of a precategory

```agda
total-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
total-hom-Precategory C =
  total-hom-Nonunital-Precategory (nonunital-precategory-Precategory C)

obj-total-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) →
  total-hom-Precategory C → obj-Precategory C × obj-Precategory C
obj-total-hom-Precategory C =
  obj-total-hom-Nonunital-Precategory (nonunital-precategory-Precategory C)
```

### Precomposition by a morphism

```agda
precomp-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) {x y : obj-Precategory C}
  (f : hom-Precategory C x y) (z : obj-Precategory C) →
  hom-Precategory C y z → hom-Precategory C x z
precomp-hom-Precategory C f z g = comp-hom-Precategory C g f
```

### Postcomposition by a morphism

```agda
postcomp-hom-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) {x y : obj-Precategory C}
  (f : hom-Precategory C x y) (z : obj-Precategory C) →
  hom-Precategory C z x → hom-Precategory C z y
postcomp-hom-Precategory C f z = comp-hom-Precategory C f
```

### Equalities give rise to homomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  hom-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → hom-Precategory C x y
  hom-eq-Precategory x .x refl = id-hom-Precategory C

  hom-inv-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → hom-Precategory C y x
  hom-inv-eq-Precategory x y = hom-eq-Precategory y x ∘ inv
```
