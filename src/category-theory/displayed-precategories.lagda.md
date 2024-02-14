# Displayed precategories

```agda
module category-theory.displayed-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.dependent-composition-operations-over-precategories
open import category-theory.nonunital-precategories
open import category-theory.precategories
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subsingleton-induction
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, a **displayed
precategory** over `C` is an associative and unital
[dependent composition structure](category-theory.dependent-composition-operations-over-precategories.md)
over it.

Thus, a displayed precategory `D` over `C` consists of

- a family of objects `ob D` indexed by `ob C`,
- a family of hom-[sets](foundation-core.sets.md)

  ```text
  hom D : hom C x y → ob D x → ob D y → Set,
  ```

  for every pair `x y : ob C`, and

- a dependent composition operation

  ```text
    comp D : hom D g y' z' → hom D f x' y' → hom D (g ∘ f) x' z'
  ```

  such that

- The dependent associativity condition

  ```text
  comp D (comp D h' g') f' ＝ comp D h' (comp D g' f')
  ```

  over the associativity witness `(h ∘ g) ∘ f ＝ h ∘ (g ∘ f)` in `C` holds, and

- the composition operation is dependent unital, meaning there is a family of
  identity morphisms

  ```text
    id D : (x : ob C) (x' : ob D x) → hom D (id C x) x' x'
  ```

  which is a dependent left and right unit in the sense that the dependent
  identities `comp D (id D) f ＝ f` and `comp D f (id D) ＝ f` hold over the
  respective witnesses of left and right unitality in `C`.

## Definitions

### The predicate of being a displayed precategory

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2)
  ( obj-D : obj-Precategory C → UU l3)
  ( hom-set-D :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) (x' : obj-D x) (y' : obj-D y) → Set l4)
  ( comp-hom-D : dependent-composition-operation-Precategory C obj-D hom-set-D)
  where

  is-displayed-precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-displayed-precategory =
    ( is-associative-dependent-composition-operation-Precategory C
        obj-D hom-set-D comp-hom-D) ×
    ( is-unital-dependent-composition-operation-Precategory C
        obj-D hom-set-D comp-hom-D)
```

### The type of displayed precategories over a precategory

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (C : Precategory l1 l2)
  where

  Displayed-Precategory : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  Displayed-Precategory =
    Σ ( obj-Precategory C → UU l3)
      ( λ obj-D →
        Σ ( {x y : obj-Precategory C}
            (f : hom-Precategory C x y) (x' : obj-D x) (y' : obj-D y) → Set l4)
          ( λ hom-set-D →
            Σ ( dependent-composition-operation-Precategory C obj-D hom-set-D)
              ( is-displayed-precategory C obj-D hom-set-D)))

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Displayed-Precategory l3 l4 C)
  where

  obj-Displayed-Precategory : obj-Precategory C → UU l3
  obj-Displayed-Precategory = pr1 D

  hom-set-Displayed-Precategory :
    {x y : obj-Precategory C} (f : hom-Precategory C x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    Set l4
  hom-set-Displayed-Precategory = pr1 (pr2 D)

  hom-Displayed-Precategory :
    {x y : obj-Precategory C} (f : hom-Precategory C x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    UU l4
  hom-Displayed-Precategory f x' y' =
    type-Set (hom-set-Displayed-Precategory f x' y')

  is-set-hom-Displayed-Precategory :
    {x y : obj-Precategory C} (f : hom-Precategory C x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    is-set (hom-Displayed-Precategory f x' y')
  is-set-hom-Displayed-Precategory f x' y' =
    is-set-type-Set (hom-set-Displayed-Precategory f x' y')

  comp-hom-Displayed-Precategory :
    dependent-composition-operation-Precategory C
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
  comp-hom-Displayed-Precategory = pr1 (pr2 (pr2 D))

  associative-comp-hom-Displayed-Precategory :
    is-associative-dependent-composition-operation-Precategory C
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
      ( comp-hom-Displayed-Precategory)
  associative-comp-hom-Displayed-Precategory = pr1 (pr2 (pr2 (pr2 D)))

  is-unital-comp-hom-Displayed-Precategory :
    is-unital-dependent-composition-operation-Precategory C
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
      ( comp-hom-Displayed-Precategory)
  is-unital-comp-hom-Displayed-Precategory = pr2 (pr2 (pr2 (pr2 D)))

  id-hom-Displayed-Precategory :
    {x : obj-Precategory C} (x' : obj-Displayed-Precategory x) →
    hom-Displayed-Precategory (id-hom-Precategory C) x' x'
  id-hom-Displayed-Precategory = pr1 is-unital-comp-hom-Displayed-Precategory

  left-unit-law-comp-hom-Displayed-Precategory :
    is-left-unit-dependent-composition-operation-Precategory C
      obj-Displayed-Precategory
      hom-set-Displayed-Precategory
      comp-hom-Displayed-Precategory
      id-hom-Displayed-Precategory
  left-unit-law-comp-hom-Displayed-Precategory =
    pr1 (pr2 is-unital-comp-hom-Displayed-Precategory)

  right-unit-law-comp-hom-Displayed-Precategory :
    is-right-unit-dependent-composition-operation-Precategory C
      obj-Displayed-Precategory
      hom-set-Displayed-Precategory
      comp-hom-Displayed-Precategory
      id-hom-Displayed-Precategory
  right-unit-law-comp-hom-Displayed-Precategory =
    pr2 (pr2 is-unital-comp-hom-Displayed-Precategory)
```

### The total precategory associated to a displayed precategory

Given a displayed precategory `D` over `C`, the total structure `∫D` whose
objects are

```text
  ob ∫D := Σ (x : ob C) (ob D x)
```

and hom-sets are

```text
  hom ∫D (x , x') (y , y') := Σ (f : hom C x y) (hom D f x' y')
```

form a precategory called the
{{#concept "total precategory" Disambiguation="of a displayed precategory" Agda=total-precategory-Displayed-Precategory}}
of `D`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Displayed-Precategory l3 l4 C)
  where

  obj-total-precategory-Displayed-Precategory : UU (l1 ⊔ l3)
  obj-total-precategory-Displayed-Precategory =
    Σ (obj-Precategory C) (obj-Displayed-Precategory C D)

  hom-set-total-precategory-Displayed-Precategory :
    (x y : obj-total-precategory-Displayed-Precategory) → Set (l2 ⊔ l4)
  hom-set-total-precategory-Displayed-Precategory (x , x') (y , y') =
    Σ-Set
      ( hom-set-Precategory C x y)
      ( λ f → hom-set-Displayed-Precategory C D f x' y')

  hom-total-precategory-Displayed-Precategory :
    (x y : obj-total-precategory-Displayed-Precategory) → UU (l2 ⊔ l4)
  hom-total-precategory-Displayed-Precategory x y =
    type-Set (hom-set-total-precategory-Displayed-Precategory x y)

  comp-hom-total-precategory-Displayed-Precategory :
    {x y z : obj-total-precategory-Displayed-Precategory} →
    hom-total-precategory-Displayed-Precategory y z →
    hom-total-precategory-Displayed-Precategory x y →
    hom-total-precategory-Displayed-Precategory x z
  pr1 (comp-hom-total-precategory-Displayed-Precategory (g , g') (f , f')) =
    comp-hom-Precategory C g f
  pr2 (comp-hom-total-precategory-Displayed-Precategory (g , g') (f , f')) =
    comp-hom-Displayed-Precategory C D g f g' f'

  associative-comp-hom-total-precategory-Displayed-Precategory :
    {x y z w : obj-total-precategory-Displayed-Precategory}
    (h : hom-total-precategory-Displayed-Precategory z w)
    (g : hom-total-precategory-Displayed-Precategory y z)
    (f : hom-total-precategory-Displayed-Precategory x y) →
    ( comp-hom-total-precategory-Displayed-Precategory
      ( comp-hom-total-precategory-Displayed-Precategory h g)
      ( f)) ＝
    ( comp-hom-total-precategory-Displayed-Precategory
      ( h)
      ( comp-hom-total-precategory-Displayed-Precategory g f))
  associative-comp-hom-total-precategory-Displayed-Precategory
    ( h , h') (g , g') (f , f') =
    eq-pair-Σ
      ( associative-comp-hom-Precategory C h g f)
      ( associative-comp-hom-Displayed-Precategory C D h g f h' g' f')

  associative-composition-operation-total-precategory-Displayed-Precategory :
    associative-composition-operation-binary-family-Set
      ( hom-set-total-precategory-Displayed-Precategory)
  pr1
    associative-composition-operation-total-precategory-Displayed-Precategory =
    comp-hom-total-precategory-Displayed-Precategory
  pr1
    ( pr2
      associative-composition-operation-total-precategory-Displayed-Precategory
        h g f) =
    associative-comp-hom-total-precategory-Displayed-Precategory h g f
  pr2
    ( pr2
      associative-composition-operation-total-precategory-Displayed-Precategory
      h g f) =
    inv (associative-comp-hom-total-precategory-Displayed-Precategory h g f)

  id-hom-total-precategory-Displayed-Precategory :
    {x : obj-total-precategory-Displayed-Precategory} →
    hom-total-precategory-Displayed-Precategory x x
  pr1 (id-hom-total-precategory-Displayed-Precategory {x , x'}) =
    id-hom-Precategory C
  pr2 (id-hom-total-precategory-Displayed-Precategory {x , x'}) =
    id-hom-Displayed-Precategory C D x'

  left-unit-law-comp-hom-total-precategory-Displayed-Precategory :
    {x y : obj-total-precategory-Displayed-Precategory} →
    (f : hom-total-precategory-Displayed-Precategory x y) →
    comp-hom-total-precategory-Displayed-Precategory
      ( id-hom-total-precategory-Displayed-Precategory)
      ( f) ＝
    f
  left-unit-law-comp-hom-total-precategory-Displayed-Precategory (f , f') =
    eq-pair-Σ
      ( left-unit-law-comp-hom-Precategory C f)
      ( left-unit-law-comp-hom-Displayed-Precategory C D f f')

  right-unit-law-comp-hom-total-precategory-Displayed-Precategory :
    {x y : obj-total-precategory-Displayed-Precategory} →
    (f : hom-total-precategory-Displayed-Precategory x y) →
    comp-hom-total-precategory-Displayed-Precategory
      ( f)
      ( id-hom-total-precategory-Displayed-Precategory) ＝
    f
  right-unit-law-comp-hom-total-precategory-Displayed-Precategory (f , f') =
    eq-pair-Σ
      ( right-unit-law-comp-hom-Precategory C f)
      ( right-unit-law-comp-hom-Displayed-Precategory C D f f')

  is-unital-composition-operation-total-precategory-Displayed-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-total-precategory-Displayed-Precategory)
      ( comp-hom-total-precategory-Displayed-Precategory)
  pr1
    is-unital-composition-operation-total-precategory-Displayed-Precategory x =
    id-hom-total-precategory-Displayed-Precategory
  pr1
    ( pr2
      is-unital-composition-operation-total-precategory-Displayed-Precategory) =
        left-unit-law-comp-hom-total-precategory-Displayed-Precategory
  pr2
    ( pr2
      is-unital-composition-operation-total-precategory-Displayed-Precategory) =
        right-unit-law-comp-hom-total-precategory-Displayed-Precategory

  total-precategory-Displayed-Precategory : Precategory (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 total-precategory-Displayed-Precategory =
    obj-total-precategory-Displayed-Precategory
  pr1 (pr2 total-precategory-Displayed-Precategory) =
    hom-set-total-precategory-Displayed-Precategory
  pr1 (pr2 (pr2 total-precategory-Displayed-Precategory)) =
    associative-composition-operation-total-precategory-Displayed-Precategory
  pr2 (pr2 (pr2 total-precategory-Displayed-Precategory)) =
    is-unital-composition-operation-total-precategory-Displayed-Precategory
```

### The fiber precategory of a displayed precategory over an object

Given a displayed precategory `D` over `C`, the fiber of `D` over `x : ob C`
defines a precategory.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Displayed-Precategory l3 l4 C)
  (c : obj-Precategory C)
  where

  obj-fiber-precategory-Displayed-Precategory : UU l3
  obj-fiber-precategory-Displayed-Precategory = obj-Displayed-Precategory C D c

  hom-set-fiber-precategory-Displayed-Precategory :
    (x y : obj-fiber-precategory-Displayed-Precategory) → Set l4
  hom-set-fiber-precategory-Displayed-Precategory =
    hom-set-Displayed-Precategory C D (id-hom-Precategory C {c})

  hom-fiber-precategory-Displayed-Precategory :
    (x y : obj-fiber-precategory-Displayed-Precategory) → UU l4
  hom-fiber-precategory-Displayed-Precategory x y =
    type-Set (hom-set-fiber-precategory-Displayed-Precategory x y)

  comp-hom-fiber-precategory-Displayed-Precategory :
    {x y z : obj-fiber-precategory-Displayed-Precategory} →
    hom-fiber-precategory-Displayed-Precategory y z →
    hom-fiber-precategory-Displayed-Precategory x y →
    hom-fiber-precategory-Displayed-Precategory x z
  comp-hom-fiber-precategory-Displayed-Precategory {x} {y} {z} g f =
    tr
      ( λ i → hom-Displayed-Precategory C D i x z)
      ( left-unit-law-comp-hom-Precategory C (id-hom-Precategory C))
      ( comp-hom-Displayed-Precategory C D
        ( id-hom-Precategory C) (id-hom-Precategory C) g f)
```

By associativity in `D`, composition in the fiber is dependently associative

```text
      f       g       h
  x ----> y ----> z ----> w

  c ===== c ===== c ===== c
```

```agda
  associative-comp-hom-fiber-precategory-Displayed-Precategory :
    {x y z w : obj-fiber-precategory-Displayed-Precategory}
    (h : hom-fiber-precategory-Displayed-Precategory z w)
    (g : hom-fiber-precategory-Displayed-Precategory y z)
    (f : hom-fiber-precategory-Displayed-Precategory x y) →
    ( comp-hom-fiber-precategory-Displayed-Precategory
      ( comp-hom-fiber-precategory-Displayed-Precategory h g)
      ( f)) ＝
    ( comp-hom-fiber-precategory-Displayed-Precategory
      ( h)
      ( comp-hom-fiber-precategory-Displayed-Precategory g f))
  associative-comp-hom-fiber-precategory-Displayed-Precategory
    {x} {y} {z} {w} h g f =
      {! associative-comp-hom-Displayed-Precategory C D _ _ _ h g f  !} -- this is a dependent identification over `associative-comp-hom-Precategory C id-hom id-hom id-hom`. Can we show it's a
      -- equational-reasoning {! comp-hom-fiber-precategory-Displayed-Precategory (comp-hom-fiber-precategory-Displayed-Precategory h g) f !} ＝ {!   !} by {!   !}
      -- ind-subsingleton
      --   ( is-set-hom-Displayed-Precategory C D
      --     ( id-hom-Precategory C {c})
      --     ( x)
      --     ( w)
      --     ( comp-hom-fiber-precategory-Displayed-Precategory
      --       ( comp-hom-fiber-precategory-Displayed-Precategory h g)
      --       ( f))
      --     ( comp-hom-fiber-precategory-Displayed-Precategory
      --       ( h)
      --       ( comp-hom-fiber-precategory-Displayed-Precategory g f)))
      --   (associative-comp-hom-Displayed-Precategory C D
      --     {c} {c} {c} {c}
      --     ( id-hom-Precategory C)
      --     ( id-hom-Precategory C)
      --     ( id-hom-Precategory C)
      --     {x} {y} {z} {w} h g f)
    -- tr
    --   (λ p → {!   !})
    --   ( eq-is-prop
    --     )
    --   ( associative-comp-hom-Displayed-Precategory C D
    --     {c} {c} {c} {c}
    --     ( id-hom-Precategory C)
    --     ( id-hom-Precategory C)
    --     ( id-hom-Precategory C)
    --     {x} {y} {z} {w} h g f)

  -- associative-composition-operation-fiber-precategory-Displayed-Precategory :
  --   associative-composition-operation-binary-family-Set
  --     ( hom-set-fiber-precategory-Displayed-Precategory)
  -- pr1
  --   associative-composition-operation-fiber-precategory-Displayed-Precategory =
  --   comp-hom-fiber-precategory-Displayed-Precategory
  -- pr2
  --   associative-composition-operation-fiber-precategory-Displayed-Precategory =
  --   associative-comp-hom-fiber-precategory-Displayed-Precategory

  -- id-hom-fiber-precategory-Displayed-Precategory :
  --   {x : obj-fiber-precategory-Displayed-Precategory} →
  --   hom-fiber-precategory-Displayed-Precategory x x
  -- id-hom-fiber-precategory-Displayed-Precategory {x} =
  --   id-hom-Displayed-Precategory C D x

  -- left-unit-law-comp-hom-fiber-precategory-Displayed-Precategory :
  --   {x y : obj-fiber-precategory-Displayed-Precategory} →
  --   (f : hom-fiber-precategory-Displayed-Precategory x y) →
  --   comp-hom-fiber-precategory-Displayed-Precategory
  --     ( id-hom-fiber-precategory-Displayed-Precategory)
  --     ( f) ＝
  --   f
  -- left-unit-law-comp-hom-fiber-precategory-Displayed-Precategory =
  --   left-unit-law-comp-hom-Displayed-Precategory C D (id-hom-Precategory C {c})

  -- right-unit-law-comp-hom-fiber-precategory-Displayed-Precategory :
  --   {x y : obj-fiber-precategory-Displayed-Precategory} →
  --   (f : hom-fiber-precategory-Displayed-Precategory x y) →
  --   comp-hom-fiber-precategory-Displayed-Precategory
  --     ( f)
  --     ( id-hom-fiber-precategory-Displayed-Precategory) ＝
  --   f
  -- right-unit-law-comp-hom-fiber-precategory-Displayed-Precategory =
  --   right-unit-law-comp-hom-Displayed-Precategory C D (id-hom-Precategory C {c})

  -- is-unital-composition-operation-fiber-precategory-Displayed-Precategory :
  --   is-unital-composition-operation-binary-family-Set
  --     ( hom-set-fiber-precategory-Displayed-Precategory)
  --     ( comp-hom-fiber-precategory-Displayed-Precategory)
  -- pr1
  --   is-unital-composition-operation-fiber-precategory-Displayed-Precategory x =
  --   id-hom-fiber-precategory-Displayed-Precategory
  -- pr1
  --   ( pr2
  --     is-unital-composition-operation-fiber-precategory-Displayed-Precategory) =
  --       left-unit-law-comp-hom-fiber-precategory-Displayed-Precategory
  -- pr2
  --   ( pr2
  --     is-unital-composition-operation-fiber-precategory-Displayed-Precategory) =
  --       right-unit-law-comp-hom-fiber-precategory-Displayed-Precategory

  -- fiber-precategory-Displayed-Precategory : Precategory l3 l4
  -- pr1 fiber-precategory-Displayed-Precategory =
  --   obj-fiber-precategory-Displayed-Precategory
  -- pr1 (pr2 fiber-precategory-Displayed-Precategory) =
  --   hom-set-fiber-precategory-Displayed-Precategory
  -- pr1 (pr2 (pr2 fiber-precategory-Displayed-Precategory)) =
  --   associative-composition-operation-fiber-precategory-Displayed-Precategory
  -- pr2 (pr2 (pr2 fiber-precategory-Displayed-Precategory)) =
  --   is-unital-composition-operation-fiber-precategory-Displayed-Precategory
```

## References

1. Benedikt Ahrens and Peter LeFanu Lumsdaine, _Displayed Categories_ (2019)
   ([arXiv:1705.04296](https://arxiv.org/abs/1705.04296))

## External links

- [Displayed Categories](https://1lab.dev/Cat.Displayed.Base.html) at 1lab
- [displayed category](https://ncatlab.org/nlab/show/displayed+category) at
  $n$Lab
- [Displayed categories](https://www.epatters.org/wiki/algebra/displayed-categories)
  at Evan Patterson's blog

A wikidata identifier was not available for this concept.
