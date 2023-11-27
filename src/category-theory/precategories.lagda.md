# Precategories

```agda
module category-theory.precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.nonunital-precategories
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
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

## Definitions

### The predicate of being a precategory on composition operations on binary families of sets

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  (comp-hom : composition-operation-binary-family-Set hom-set)
  where

  is-precategory-prop-composition-operation-binary-family-Set : Prop (l1 ⊔ l2)
  is-precategory-prop-composition-operation-binary-family-Set =
    prod-Prop
      ( is-unital-prop-composition-operation-binary-family-Set hom-set comp-hom)
      ( is-associative-prop-composition-operation-binary-family-Set
        ( hom-set)
        ( comp-hom))

  is-precategory-composition-operation-binary-family-Set : UU (l1 ⊔ l2)
  is-precategory-composition-operation-binary-family-Set =
    type-Prop is-precategory-prop-composition-operation-binary-family-Set

  is-prop-is-precategory-composition-operation-binary-family-Set :
    is-prop is-precategory-composition-operation-binary-family-Set
  is-prop-is-precategory-composition-operation-binary-family-Set =
    is-prop-type-Prop
      is-precategory-prop-composition-operation-binary-family-Set
```

### The type of precategories

```agda
Precategory :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Precategory l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → Set l2)
        ( λ hom-set →
          Σ ( associative-composition-operation-binary-family-Set hom-set)
            ( λ (comp-hom , assoc-comp) →
              is-unital-composition-operation-binary-family-Set
                ( hom-set)
                ( comp-hom))))

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

  associative-composition-operation-Precategory :
    associative-composition-operation-binary-family-Set hom-set-Precategory
  associative-composition-operation-Precategory = pr1 (pr2 (pr2 C))

  comp-hom-Precategory :
    {x y z : obj-Precategory} →
    hom-Precategory y z →
    hom-Precategory x y →
    hom-Precategory x z
  comp-hom-Precategory =
    comp-hom-associative-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( associative-composition-operation-Precategory)

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
    witness-associative-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( associative-composition-operation-Precategory)

  inv-associative-comp-hom-Precategory :
    {x y z w : obj-Precategory}
    (h : hom-Precategory z w)
    (g : hom-Precategory y z)
    (f : hom-Precategory x y) →
    ( comp-hom-Precategory h (comp-hom-Precategory g f)) ＝
    ( comp-hom-Precategory (comp-hom-Precategory h g) f)
  inv-associative-comp-hom-Precategory =
    inv-witness-associative-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( associative-composition-operation-Precategory)

  is-unital-composition-operation-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( comp-hom-Precategory)
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
  pr2 (pr2 nonunital-precategory-Precategory) =
    associative-composition-operation-Precategory C
```

### The underlying set-magmoid of a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  set-magmoid-Precategory : Set-Magmoid l1 l2
  set-magmoid-Precategory =
    set-magmoid-Nonunital-Precategory (nonunital-precategory-Precategory C)
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

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  hom-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → hom-Precategory C x y
  hom-eq-Precategory x .x refl = id-hom-Precategory C

  hom-inv-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → hom-Precategory C y x
  hom-inv-eq-Precategory x y = hom-eq-Precategory y x ∘ inv
```

### Pre- and postcomposition by a morphism

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : hom-Precategory C x y)
  (z : obj-Precategory C)
  where

  precomp-hom-Precategory : hom-Precategory C y z → hom-Precategory C x z
  precomp-hom-Precategory g = comp-hom-Precategory C g f

  postcomp-hom-Precategory : hom-Precategory C z x → hom-Precategory C z y
  postcomp-hom-Precategory = comp-hom-Precategory C f
```

## Properties

### If the objects of a precategory are `k`-truncated for non-negative `k`, the total hom-type is `k`-truncated

```agda
module _
  {l1 l2 : Level} {k : 𝕋} (C : Precategory l1 l2)
  where

  is-trunc-total-hom-is-trunc-obj-Precategory :
    is-trunc (succ-𝕋 (succ-𝕋 k)) (obj-Precategory C) →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (total-hom-Precategory C)
  is-trunc-total-hom-is-trunc-obj-Precategory =
    is-trunc-total-hom-is-trunc-obj-Nonunital-Precategory
      ( nonunital-precategory-Precategory C)

  total-hom-truncated-type-is-trunc-obj-Precategory :
    is-trunc (succ-𝕋 (succ-𝕋 k)) (obj-Precategory C) →
    Truncated-Type (l1 ⊔ l2) (succ-𝕋 (succ-𝕋 k))
  total-hom-truncated-type-is-trunc-obj-Precategory =
    total-hom-truncated-type-is-trunc-obj-Nonunital-Precategory
      ( nonunital-precategory-Precategory C)
```

## See also

- [Categories](category-theory.categories.md) are univalent precategories.
- [Functors between precategories](category-theory.categories.md) are
  [structure](foundation.structure.md)-preserving maps of precategories.
- [Large precategories](category-theory.large-precategories.md) are
  precategories whose collection of objects form a large type.

## External links

- [Precategories](https://1lab.dev/Cat.Base.html) at 1lab
- [precategory](https://ncatlab.org/nlab/show/precategory) at $n$Lab
