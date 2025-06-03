# Dependent composition operations over precategories

```agda
module category-theory.dependent-composition-operations-over-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.nonunital-precategories
open import category-theory.precategories
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, a
{{#concept "dependent composition structure" Disambiguation="over a precategory"}}
`D` over `C` is a family of types `obj D` over `obj C` and a family of
_hom-[sets](foundation-core.sets.md)_

```text
hom D : hom C x y → obj D x → obj D y → Set
```

for every pair `x y : obj C`, equipped with a
{{#concept "dependent composition operation" Disambiguation="over a precategory" Agda=dependent-composition-operation-Precategory}}

```text
  comp D : hom D g y' z' → hom D f x' y' → hom D (g ∘ f) x' z'.
```

## Definitions

### The type of dependent composition operations over a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  dependent-composition-operation-Precategory :
    { l3 l4 : Level}
    ( obj-D : obj-Precategory C → UU l3) →
    ( hom-set-D :
      {x y : obj-Precategory C}
      (f : hom-Precategory C x y)
      (x' : obj-D x) (y' : obj-D y) → Set l4) →
      UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  dependent-composition-operation-Precategory obj-D hom-set-D =
    {x y z : obj-Precategory C}
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    {x' : obj-D x} {y' : obj-D y} {z' : obj-D z} →
    (g' : type-Set (hom-set-D g y' z')) (f' : type-Set (hom-set-D f x' y')) →
    type-Set (hom-set-D (comp-hom-Precategory C g f) x' z')
```

### The predicate of being associative on dependent composition operations over a precategory

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2)
  ( obj-D : obj-Precategory C → UU l3)
  ( hom-set-D :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) (x' : obj-D x) (y' : obj-D y) → Set l4)
  ( comp-hom-D : dependent-composition-operation-Precategory C obj-D hom-set-D)
  where

  is-associative-dependent-composition-operation-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-associative-dependent-composition-operation-Precategory =
    {x y z w : obj-Precategory C}
    (h : hom-Precategory C z w)
    (g : hom-Precategory C y z)
    (f : hom-Precategory C x y)
    {x' : obj-D x} {y' : obj-D y} {z' : obj-D z} {w' : obj-D w}
    (h' : type-Set (hom-set-D h z' w'))
    (g' : type-Set (hom-set-D g y' z'))
    (f' : type-Set (hom-set-D f x' y')) →
    dependent-identification
      ( λ i → type-Set (hom-set-D i x' w'))
      ( associative-comp-hom-Precategory C h g f)
      ( comp-hom-D (comp-hom-Precategory C h g) f (comp-hom-D h g h' g') f')
      ( comp-hom-D h (comp-hom-Precategory C g f) h' (comp-hom-D g f g' f'))

  is-prop-is-associative-dependent-composition-operation-Precategory :
    is-prop is-associative-dependent-composition-operation-Precategory
  is-prop-is-associative-dependent-composition-operation-Precategory =
    is-prop-iterated-implicit-Π 4
      ( λ x y z w →
        is-prop-iterated-Π 3
          ( λ h g f →
            is-prop-iterated-implicit-Π 4
              ( λ x' y' z' w' →
                is-prop-iterated-Π 3
                  ( λ h' g' f' →
                    is-set-type-Set
                      ( hom-set-D
                        ( comp-hom-Precategory C h (comp-hom-Precategory C g f))
                        ( x')
                        ( w'))
                      ( tr
                        ( λ i → type-Set (hom-set-D i x' w'))
                        ( associative-comp-hom-Precategory C h g f)
                        ( comp-hom-D
                          ( comp-hom-Precategory C h g)
                          ( f)
                          ( comp-hom-D h g h' g')
                          ( f')))
                      ( comp-hom-D
                        ( h)
                        ( comp-hom-Precategory C g f)
                        ( h')
                        ( comp-hom-D g f g' f'))))))

  is-associative-prop-dependent-composition-operation-Precategory :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-associative-prop-dependent-composition-operation-Precategory =
    is-associative-dependent-composition-operation-Precategory
  pr2 is-associative-prop-dependent-composition-operation-Precategory =
    is-prop-is-associative-dependent-composition-operation-Precategory
```

### The predicate of being unital on dependent composition operations over a precategory

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2)
  ( obj-D : obj-Precategory C → UU l3)
  ( hom-set-D :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) (x' : obj-D x) (y' : obj-D y) → Set l4)
  ( comp-hom-D : dependent-composition-operation-Precategory C obj-D hom-set-D)
  ( id-hom-D :
    {x : obj-Precategory C} (x' : obj-D x) →
    type-Set (hom-set-D (id-hom-Precategory C {x}) x' x'))
  where

  is-left-unit-dependent-composition-operation-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-left-unit-dependent-composition-operation-Precategory =
    {x y : obj-Precategory C} (f : hom-Precategory C x y)
    {x' : obj-D x} {y' : obj-D y} (f' : type-Set (hom-set-D f x' y')) →
    dependent-identification
      ( λ i → type-Set (hom-set-D i x' y'))
      ( left-unit-law-comp-hom-Precategory C f)
      ( comp-hom-D (id-hom-Precategory C) f (id-hom-D y') f')
      ( f')

  is-prop-is-left-unit-dependent-composition-operation-Precategory :
    is-prop is-left-unit-dependent-composition-operation-Precategory
  is-prop-is-left-unit-dependent-composition-operation-Precategory =
    is-prop-iterated-implicit-Π 2
      ( λ x y →
        is-prop-Π
          ( λ f →
            is-prop-iterated-implicit-Π 2
              ( λ x' y' →
                is-prop-Π
                  ( λ f' →
                    is-set-type-Set
                      ( hom-set-D f x' y')
                      ( tr
                        ( λ i → type-Set (hom-set-D i x' y'))
                        ( left-unit-law-comp-hom-Precategory C f)
                        ( comp-hom-D (id-hom-Precategory C) f (id-hom-D y') f'))
                      ( f')))))

  is-left-unit-prop-dependent-composition-operation-Precategory :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-left-unit-prop-dependent-composition-operation-Precategory =
    is-left-unit-dependent-composition-operation-Precategory
  pr2 is-left-unit-prop-dependent-composition-operation-Precategory =
    is-prop-is-left-unit-dependent-composition-operation-Precategory

  is-right-unit-dependent-composition-operation-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-right-unit-dependent-composition-operation-Precategory =
    {x y : obj-Precategory C} (f : hom-Precategory C x y)
    {x' : obj-D x} {y' : obj-D y} (f' : type-Set (hom-set-D f x' y')) →
    dependent-identification
      ( λ i → type-Set (hom-set-D i x' y'))
      ( right-unit-law-comp-hom-Precategory C f)
      ( comp-hom-D f (id-hom-Precategory C) f' (id-hom-D x'))
      ( f')

  is-prop-is-right-unit-dependent-composition-operation-Precategory :
    is-prop is-right-unit-dependent-composition-operation-Precategory
  is-prop-is-right-unit-dependent-composition-operation-Precategory =
    is-prop-iterated-implicit-Π 2
      ( λ x y →
        is-prop-Π
          ( λ f →
            is-prop-iterated-implicit-Π 2
              ( λ x' y' →
                is-prop-Π
                  ( λ f' →
                    is-set-type-Set
                      ( hom-set-D f x' y')
                      ( tr
                        ( λ i → type-Set (hom-set-D i x' y'))
                        ( right-unit-law-comp-hom-Precategory C f)
                        ( comp-hom-D f (id-hom-Precategory C) f' (id-hom-D x')))
                      ( f')))))

  is-right-unit-prop-dependent-composition-operation-Precategory :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-right-unit-prop-dependent-composition-operation-Precategory =
    is-right-unit-dependent-composition-operation-Precategory
  pr2 is-right-unit-prop-dependent-composition-operation-Precategory =
    is-prop-is-right-unit-dependent-composition-operation-Precategory

  is-unit-dependent-composition-operation-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-unit-dependent-composition-operation-Precategory =
    ( is-left-unit-dependent-composition-operation-Precategory) ×
    ( is-right-unit-dependent-composition-operation-Precategory)

  is-prop-is-unit-dependent-composition-operation-Precategory :
    is-prop is-unit-dependent-composition-operation-Precategory
  is-prop-is-unit-dependent-composition-operation-Precategory =
    is-prop-product
      ( is-prop-is-left-unit-dependent-composition-operation-Precategory)
      ( is-prop-is-right-unit-dependent-composition-operation-Precategory)

  is-unit-prop-dependent-composition-operation-Precategory :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-unit-prop-dependent-composition-operation-Precategory =
    is-unit-dependent-composition-operation-Precategory
  pr2 is-unit-prop-dependent-composition-operation-Precategory =
    is-prop-is-unit-dependent-composition-operation-Precategory

module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2)
  ( obj-D : obj-Precategory C → UU l3)
  ( hom-set-D :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) (x' : obj-D x) (y' : obj-D y) → Set l4)
  ( comp-hom-D : dependent-composition-operation-Precategory C obj-D hom-set-D)
  where

  is-unital-dependent-composition-operation-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-unital-dependent-composition-operation-Precategory =
    Σ ( {x : obj-Precategory C} (x' : obj-D x) →
        type-Set (hom-set-D (id-hom-Precategory C {x}) x' x'))
      ( is-unit-dependent-composition-operation-Precategory C
          obj-D hom-set-D comp-hom-D)
```

## See also

- [Displayed precategories](category-theory.displayed-precategories.md)
