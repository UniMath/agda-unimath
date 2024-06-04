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

Given a [precategory](category-theory.precategories.md) `𝒞`, a
{{#concept "displayed precategory" Agda=Displayed-Precategory}} over `𝒞` is an
associative and unital
[dependent composition structure](category-theory.dependent-composition-operations-over-precategories.md)
over it.

Thus, a displayed precategory `𝒟` over `𝒞` consists of

- a family of objects `ob 𝒟` indexed by `ob 𝒞`,
- a family of hom-[sets](foundation-core.sets.md)

  ```text
  hom 𝒟 : hom 𝒞 x y → ob 𝒟 x → ob 𝒟 y → Set,
  ```

  for every pair `x y : ob 𝒞`, and

- a dependent composition operation

  ```text
    comp 𝒟 : hom 𝒟 g y' z' → hom 𝒟 f x' y' → hom 𝒟 (g ∘ f) x' z'
  ```

  such that

- The dependent associativity condition

  ```text
  comp 𝒟 (comp 𝒟 h' g') f' ＝ comp 𝒟 h' (comp 𝒟 g' f')
  ```

  over the associativity witness `(h ∘ g) ∘ f ＝ h ∘ (g ∘ f)` in `𝒞` holds, and

- the composition operation is dependent unital, meaning there is a family of
  identity morphisms

  ```text
    id 𝒟 : (x : ob 𝒞) (x' : ob 𝒟 x) → hom 𝒟 (id 𝒞 x) x' x'
  ```

  which is a dependent left and right unit in the sense that the dependent
  identities `comp 𝒟 (id 𝒟) f ＝ f` and `comp 𝒟 f (id 𝒟) ＝ f` hold over the
  respective witnesses of left and right unitality in `𝒞`.

## Definitions

### The predicate of being a displayed precategory

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒞 : Precategory l1 l2)
  ( obj-𝒟 : obj-Precategory 𝒞 → UU l3)
  ( hom-set-𝒟 :
    {x y : obj-Precategory 𝒞}
    (f : hom-Precategory 𝒞 x y) (x' : obj-𝒟 x) (y' : obj-𝒟 y) → Set l4)
  ( comp-hom-𝒟 : dependent-composition-operation-Precategory 𝒞 obj-𝒟 hom-set-𝒟)
  where

  is-displayed-precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-displayed-precategory =
    ( is-associative-dependent-composition-operation-Precategory 𝒞
        obj-𝒟 hom-set-𝒟 comp-hom-𝒟) ×
    ( is-unital-dependent-composition-operation-Precategory 𝒞
        obj-𝒟 hom-set-𝒟 comp-hom-𝒟)
```

### The type of displayed precategories over a precategory

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (𝒞 : Precategory l1 l2)
  where

  Displayed-Precategory : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  Displayed-Precategory =
    Σ ( obj-Precategory 𝒞 → UU l3)
      ( λ obj-𝒟 →
        Σ ( {x y : obj-Precategory 𝒞}
            (f : hom-Precategory 𝒞 x y) (x' : obj-𝒟 x) (y' : obj-𝒟 y) → Set l4)
          ( λ hom-set-𝒟 →
            Σ ( dependent-composition-operation-Precategory 𝒞 obj-𝒟 hom-set-𝒟)
              ( is-displayed-precategory 𝒞 obj-𝒟 hom-set-𝒟)))

module _
  {l1 l2 l3 l4 : Level}
  (𝒞 : Precategory l1 l2) (𝒟 : Displayed-Precategory l3 l4 𝒞)
  where

  obj-Displayed-Precategory : obj-Precategory 𝒞 → UU l3
  obj-Displayed-Precategory = pr1 𝒟

  hom-set-Displayed-Precategory :
    {x y : obj-Precategory 𝒞} (f : hom-Precategory 𝒞 x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    Set l4
  hom-set-Displayed-Precategory = pr1 (pr2 𝒟)

  hom-Displayed-Precategory :
    {x y : obj-Precategory 𝒞} (f : hom-Precategory 𝒞 x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    UU l4
  hom-Displayed-Precategory f x' y' =
    type-Set (hom-set-Displayed-Precategory f x' y')

  is-set-hom-Displayed-Precategory :
    {x y : obj-Precategory 𝒞} (f : hom-Precategory 𝒞 x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    is-set (hom-Displayed-Precategory f x' y')
  is-set-hom-Displayed-Precategory f x' y' =
    is-set-type-Set (hom-set-Displayed-Precategory f x' y')

  comp-hom-Displayed-Precategory :
    dependent-composition-operation-Precategory 𝒞
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
  comp-hom-Displayed-Precategory = pr1 (pr2 (pr2 𝒟))

  associative-comp-hom-Displayed-Precategory :
    is-associative-dependent-composition-operation-Precategory 𝒞
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
      ( comp-hom-Displayed-Precategory)
  associative-comp-hom-Displayed-Precategory = pr1 (pr2 (pr2 (pr2 𝒟)))

  is-unital-comp-hom-Displayed-Precategory :
    is-unital-dependent-composition-operation-Precategory 𝒞
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
      ( comp-hom-Displayed-Precategory)
  is-unital-comp-hom-Displayed-Precategory = pr2 (pr2 (pr2 (pr2 𝒟)))

  id-hom-Displayed-Precategory :
    {x : obj-Precategory 𝒞} (x' : obj-Displayed-Precategory x) →
    hom-Displayed-Precategory (id-hom-Precategory 𝒞) x' x'
  id-hom-Displayed-Precategory = pr1 is-unital-comp-hom-Displayed-Precategory

  left-unit-law-comp-hom-Displayed-Precategory :
    is-left-unit-dependent-composition-operation-Precategory 𝒞
      obj-Displayed-Precategory
      hom-set-Displayed-Precategory
      comp-hom-Displayed-Precategory
      id-hom-Displayed-Precategory
  left-unit-law-comp-hom-Displayed-Precategory =
    pr1 (pr2 is-unital-comp-hom-Displayed-Precategory)

  right-unit-law-comp-hom-Displayed-Precategory :
    is-right-unit-dependent-composition-operation-Precategory 𝒞
      obj-Displayed-Precategory
      hom-set-Displayed-Precategory
      comp-hom-Displayed-Precategory
      id-hom-Displayed-Precategory
  right-unit-law-comp-hom-Displayed-Precategory =
    pr2 (pr2 is-unital-comp-hom-Displayed-Precategory)
```

### The total precategory associated to a displayed precategory

Given a displayed precategory `𝒟` over `𝒞`, the total structure `∫D` whose
objects are

```text
  ob ∫D := Σ (x : ob 𝒞) (ob 𝒟 x)
```

and hom-sets are

```text
  hom ∫D (x , x') (y , y') := Σ (f : hom 𝒞 x y) (hom 𝒟 f x' y')
```

form a precategory called the
{{#concept "total precategory" Disambiguation="of a displayed precategory" Agda=total-precategory-Displayed-Precategory}}
of `𝒟`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝒞 : Precategory l1 l2) (𝒟 : Displayed-Precategory l3 l4 𝒞)
  where

  obj-total-precategory-Displayed-Precategory : UU (l1 ⊔ l3)
  obj-total-precategory-Displayed-Precategory =
    Σ (obj-Precategory 𝒞) (obj-Displayed-Precategory 𝒞 𝒟)

  hom-set-total-precategory-Displayed-Precategory :
    (x y : obj-total-precategory-Displayed-Precategory) → Set (l2 ⊔ l4)
  hom-set-total-precategory-Displayed-Precategory (x , x') (y , y') =
    Σ-Set
      ( hom-set-Precategory 𝒞 x y)
      ( λ f → hom-set-Displayed-Precategory 𝒞 𝒟 f x' y')

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
    comp-hom-Precategory 𝒞 g f
  pr2 (comp-hom-total-precategory-Displayed-Precategory (g , g') (f , f')) =
    comp-hom-Displayed-Precategory 𝒞 𝒟 g f g' f'

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
      ( associative-comp-hom-Precategory 𝒞 h g f)
      ( associative-comp-hom-Displayed-Precategory 𝒞 𝒟 h g f h' g' f')

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
    id-hom-Precategory 𝒞
  pr2 (id-hom-total-precategory-Displayed-Precategory {x , x'}) =
    id-hom-Displayed-Precategory 𝒞 𝒟 x'

  left-unit-law-comp-hom-total-precategory-Displayed-Precategory :
    {x y : obj-total-precategory-Displayed-Precategory} →
    (f : hom-total-precategory-Displayed-Precategory x y) →
    comp-hom-total-precategory-Displayed-Precategory
      ( id-hom-total-precategory-Displayed-Precategory)
      ( f) ＝
    f
  left-unit-law-comp-hom-total-precategory-Displayed-Precategory (f , f') =
    eq-pair-Σ
      ( left-unit-law-comp-hom-Precategory 𝒞 f)
      ( left-unit-law-comp-hom-Displayed-Precategory 𝒞 𝒟 f f')

  right-unit-law-comp-hom-total-precategory-Displayed-Precategory :
    {x y : obj-total-precategory-Displayed-Precategory} →
    (f : hom-total-precategory-Displayed-Precategory x y) →
    comp-hom-total-precategory-Displayed-Precategory
      ( f)
      ( id-hom-total-precategory-Displayed-Precategory) ＝
    f
  right-unit-law-comp-hom-total-precategory-Displayed-Precategory (f , f') =
    eq-pair-Σ
      ( right-unit-law-comp-hom-Precategory 𝒞 f)
      ( right-unit-law-comp-hom-Displayed-Precategory 𝒞 𝒟 f f')

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

Given a displayed precategory `𝒟` over `𝒞`, the fiber of `𝒟` over `x : ob 𝒞`
defines a precategory.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (𝒞 : Precategory l1 l2) (𝒟 : Displayed-Precategory l3 l4 𝒞)
  (c : obj-Precategory 𝒞)
  where

  obj-fiber-precategory-Displayed-Precategory : UU l3
  obj-fiber-precategory-Displayed-Precategory = obj-Displayed-Precategory 𝒞 𝒟 c

  hom-set-fiber-precategory-Displayed-Precategory :
    (x y : obj-fiber-precategory-Displayed-Precategory) → Set l4
  hom-set-fiber-precategory-Displayed-Precategory =
    hom-set-Displayed-Precategory 𝒞 𝒟 (id-hom-Precategory 𝒞 {c})

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
      ( λ i → hom-Displayed-Precategory 𝒞 𝒟 i x z)
      ( left-unit-law-comp-hom-Precategory 𝒞 (id-hom-Precategory 𝒞))
      ( comp-hom-Displayed-Precategory 𝒞 𝒟
        ( id-hom-Precategory 𝒞) (id-hom-Precategory 𝒞) g f)
```

By associativity in `𝒟`, composition in the fiber is dependently associative

```text
      f       g       h
  x ----> y ----> z ----> w

  c ===== c ===== c ===== c
```

The proof remains to be formalized.

```text
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
      {! associative-comp-hom-Displayed-Precategory 𝒞 𝒟 _ _ _ h g f  !}
```

```text
  associative-composition-operation-fiber-precategory-Displayed-Precategory :
    associative-composition-operation-binary-family-Set
      ( hom-set-fiber-precategory-Displayed-Precategory)
  pr1
    associative-composition-operation-fiber-precategory-Displayed-Precategory =
    comp-hom-fiber-precategory-Displayed-Precategory
  pr2
    associative-composition-operation-fiber-precategory-Displayed-Precategory =
    associative-comp-hom-fiber-precategory-Displayed-Precategory

  id-hom-fiber-precategory-Displayed-Precategory :
    {x : obj-fiber-precategory-Displayed-Precategory} →
    hom-fiber-precategory-Displayed-Precategory x x
  id-hom-fiber-precategory-Displayed-Precategory {x} =
    id-hom-Displayed-Precategory 𝒞 𝒟 x

  left-unit-law-comp-hom-fiber-precategory-Displayed-Precategory :
    {x y : obj-fiber-precategory-Displayed-Precategory} →
    (f : hom-fiber-precategory-Displayed-Precategory x y) →
    comp-hom-fiber-precategory-Displayed-Precategory
      ( id-hom-fiber-precategory-Displayed-Precategory)
      ( f) ＝
    f
  left-unit-law-comp-hom-fiber-precategory-Displayed-Precategory =
    left-unit-law-comp-hom-Displayed-Precategory 𝒞 𝒟 (id-hom-Precategory 𝒞 {c})

  right-unit-law-comp-hom-fiber-precategory-Displayed-Precategory :
    {x y : obj-fiber-precategory-Displayed-Precategory} →
    (f : hom-fiber-precategory-Displayed-Precategory x y) →
    comp-hom-fiber-precategory-Displayed-Precategory
      ( f)
      ( id-hom-fiber-precategory-Displayed-Precategory) ＝
    f
  right-unit-law-comp-hom-fiber-precategory-Displayed-Precategory =
    right-unit-law-comp-hom-Displayed-Precategory 𝒞 𝒟 (id-hom-Precategory 𝒞 {c})

  is-unital-composition-operation-fiber-precategory-Displayed-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-fiber-precategory-Displayed-Precategory)
      ( comp-hom-fiber-precategory-Displayed-Precategory)
  pr1
    is-unital-composition-operation-fiber-precategory-Displayed-Precategory x =
    id-hom-fiber-precategory-Displayed-Precategory
  pr1
    ( pr2
      is-unital-composition-operation-fiber-precategory-Displayed-Precategory) =
        left-unit-law-comp-hom-fiber-precategory-Displayed-Precategory
  pr2
    ( pr2
      is-unital-composition-operation-fiber-precategory-Displayed-Precategory) =
        right-unit-law-comp-hom-fiber-precategory-Displayed-Precategory

  fiber-precategory-Displayed-Precategory : Precategory l3 l4
  pr1 fiber-precategory-Displayed-Precategory =
    obj-fiber-precategory-Displayed-Precategory
  pr1 (pr2 fiber-precategory-Displayed-Precategory) =
    hom-set-fiber-precategory-Displayed-Precategory
  pr1 (pr2 (pr2 fiber-precategory-Displayed-Precategory)) =
    associative-composition-operation-fiber-precategory-Displayed-Precategory
  pr2 (pr2 (pr2 fiber-precategory-Displayed-Precategory)) =
    is-unital-composition-operation-fiber-precategory-Displayed-Precategory
```

## References

{{#bibliography}} {{#reference AL19}}

## External links

- [Displayed Categories](https://1lab.dev/Cat.Displayed.Base.html) at 1lab
- [displayed category](https://ncatlab.org/nlab/show/displayed+category) at
  $n$Lab
- [Displayed categories](https://www.epatters.org/wiki/algebra/displayed-categories)
  at Evan Patterson's blog

A wikidata identifier was not available for this concept.
