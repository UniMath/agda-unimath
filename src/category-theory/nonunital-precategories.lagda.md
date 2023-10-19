# Nonunital precategories

```agda
module category-theory.nonunital-precategories where
```

<details><summary>Imports</summary>

```agda
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

A **nonunital precategory** is a [precategory](category-theory.precategories.md)
that may not have identity maps. Such an object may also rightfully be called a
_semiprecategory_.

## Definition

### Associative composition structures on sets

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom : A → A → Set l2)
  where

  composition-operation-Set : UU (l1 ⊔ l2)
  composition-operation-Set =
    {x y z : A} → type-Set (hom y z) → type-Set (hom x y) → type-Set (hom x z)

  associativity-composition-operation-Set :
    composition-operation-Set → UU (l1 ⊔ l2)
  associativity-composition-operation-Set μ =
    {x y z w : A} (h : type-Set (hom z w)) (g : type-Set (hom y z))
    (f : type-Set (hom x y)) → μ (μ h g) f ＝ μ h (μ g f)

  associative-composition-structure-Set : UU (l1 ⊔ l2)
  associative-composition-structure-Set =
    Σ ( composition-operation-Set)
      ( associativity-composition-operation-Set)
```

### Nonunital precategories

```agda
Nonunital-Precategory :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Nonunital-Precategory l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → Set l2)
        ( associative-composition-structure-Set))

module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  where

  obj-Nonunital-Precategory : UU l1
  obj-Nonunital-Precategory = pr1 C

  hom-set-Nonunital-Precategory : (x y : obj-Nonunital-Precategory) → Set l2
  hom-set-Nonunital-Precategory = pr1 (pr2 C)

  hom-Nonunital-Precategory : (x y : obj-Nonunital-Precategory) → UU l2
  hom-Nonunital-Precategory x y = type-Set (hom-set-Nonunital-Precategory x y)

  is-set-hom-Nonunital-Precategory :
    (x y : obj-Nonunital-Precategory) → is-set (hom-Nonunital-Precategory x y)
  is-set-hom-Nonunital-Precategory x y =
    is-set-type-Set (hom-set-Nonunital-Precategory x y)

  associative-composition-structure-Nonunital-Precategory :
    associative-composition-structure-Set hom-set-Nonunital-Precategory
  associative-composition-structure-Nonunital-Precategory = pr2 (pr2 C)

  comp-hom-Nonunital-Precategory :
    {x y z : obj-Nonunital-Precategory} →
    hom-Nonunital-Precategory y z →
    hom-Nonunital-Precategory x y →
    hom-Nonunital-Precategory x z
  comp-hom-Nonunital-Precategory =
    pr1 associative-composition-structure-Nonunital-Precategory

  comp-hom-Nonunital-Precategory' :
    {x y z : obj-Nonunital-Precategory} →
    hom-Nonunital-Precategory x y →
    hom-Nonunital-Precategory y z →
    hom-Nonunital-Precategory x z
  comp-hom-Nonunital-Precategory' f g = comp-hom-Nonunital-Precategory g f

  associative-comp-hom-Nonunital-Precategory :
    {x y z w : obj-Nonunital-Precategory}
    (h : hom-Nonunital-Precategory z w)
    (g : hom-Nonunital-Precategory y z)
    (f : hom-Nonunital-Precategory x y) →
    ( comp-hom-Nonunital-Precategory (comp-hom-Nonunital-Precategory h g) f) ＝
    ( comp-hom-Nonunital-Precategory h (comp-hom-Nonunital-Precategory g f))
  associative-comp-hom-Nonunital-Precategory =
    pr2 associative-composition-structure-Nonunital-Precategory
```

### The total hom-type of a nonunital precategory

```agda
total-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2) → UU (l1 ⊔ l2)
total-hom-Nonunital-Precategory C =
  Σ ( obj-Nonunital-Precategory C)
    ( λ x → Σ (obj-Nonunital-Precategory C) (hom-Nonunital-Precategory C x))

obj-total-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2) →
  total-hom-Nonunital-Precategory C →
  obj-Nonunital-Precategory C × obj-Nonunital-Precategory C
pr1 (obj-total-hom-Nonunital-Precategory C (x , y , f)) = x
pr2 (obj-total-hom-Nonunital-Precategory C (x , y , f)) = y
```

### Precomposition by a morphism

```agda
precomp-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  {x y : obj-Nonunital-Precategory C}
  (f : hom-Nonunital-Precategory C x y) (z : obj-Nonunital-Precategory C) →
  hom-Nonunital-Precategory C y z → hom-Nonunital-Precategory C x z
precomp-hom-Nonunital-Precategory C f z g = comp-hom-Nonunital-Precategory C g f
```

### Postcomposition by a morphism

```agda
postcomp-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  {x y : obj-Nonunital-Precategory C}
  (f : hom-Nonunital-Precategory C x y) (z : obj-Nonunital-Precategory C) →
  hom-Nonunital-Precategory C z x → hom-Nonunital-Precategory C z y
postcomp-hom-Nonunital-Precategory C f z = comp-hom-Nonunital-Precategory C f
```

### Unital composition structures

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom : A → A → Set l2)
  where

  is-unital-composition-operation-Set :
    composition-operation-Set hom → UU (l1 ⊔ l2)
  is-unital-composition-operation-Set μ =
    Σ ( (x : A) → type-Set (hom x x))
      ( λ e →
        ( {x y : A} (f : type-Set (hom x y)) → μ (e y) f ＝ f) ×
        ( {x y : A} (f : type-Set (hom x y)) → μ f (e x) ＝ f))

module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  where

  is-unital-Nonunital-Precategory : UU (l1 ⊔ l2)
  is-unital-Nonunital-Precategory =
    is-unital-composition-operation-Set
      ( hom-set-Nonunital-Precategory C)
      ( comp-hom-Nonunital-Precategory C)
```

## Properties

### Being unital is a property

Suppose `e e' : (x : A) → hom x x` are both right and left units with regard to
composition. It is enough to show that `e = e'` since the right and left unit
laws are propositions (because all hom-types are sets). By function
extensionality, it is enough to show that `e x = e' x` for all `x : A`. But by
the unit laws we have the following chain of equalities:
`e x = (e' x) ∘ (e x) = e' x.`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (hom : A → A → Set l2)
  where

  abstract
    all-elements-equal-is-unital-composition-operation-Set :
      ( μ : composition-operation-Set hom) →
      all-elements-equal (is-unital-composition-operation-Set hom μ)
    all-elements-equal-is-unital-composition-operation-Set
      ( μ)
      ( e , left-unit-law-e , right-unit-law-e)
      ( e' , left-unit-law-e' , right-unit-law-e') =
      eq-type-subtype
        ( λ x →
          prod-Prop
            ( Π-Prop' A
              ( λ a →
                Π-Prop' A
                  ( λ b →
                    Π-Prop
                      ( type-Set (hom a b))
                      ( λ f' → Id-Prop (hom a b) (μ (x b) f') f'))))
            ( Π-Prop' A
              ( λ a →
                Π-Prop' A
                  ( λ b →
                    Π-Prop
                      ( type-Set (hom a b))
                      ( λ f' → Id-Prop (hom a b) (μ f' (x a)) f')))))
        ( eq-htpy
          ( λ x → inv (left-unit-law-e' (e x)) ∙ right-unit-law-e (e' x)))

    is-prop-is-unital-composition-operation-Set :
      ( μ : composition-operation-Set hom) →
      is-prop (is-unital-composition-operation-Set hom μ)
    is-prop-is-unital-composition-operation-Set μ =
      is-prop-all-elements-equal
        ( all-elements-equal-is-unital-composition-operation-Set μ)

    is-unital-prop-composition-operation-Set :
      ( μ : composition-operation-Set hom) → Prop (l1 ⊔ l2)
    pr1 (is-unital-prop-composition-operation-Set μ) =
      is-unital-composition-operation-Set hom μ
    pr2 (is-unital-prop-composition-operation-Set μ) =
      is-prop-is-unital-composition-operation-Set μ

module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  where

  is-prop-is-unital-Nonunital-Precategory :
    is-prop
      ( is-unital-composition-operation-Set
        ( hom-set-Nonunital-Precategory C)
        ( comp-hom-Nonunital-Precategory C))
  is-prop-is-unital-Nonunital-Precategory =
    is-prop-is-unital-composition-operation-Set
      ( hom-set-Nonunital-Precategory C)
      ( comp-hom-Nonunital-Precategory C)

  is-unital-prop-Nonunital-Precategory : Prop (l1 ⊔ l2)
  is-unital-prop-Nonunital-Precategory =
    is-unital-prop-composition-operation-Set
      ( hom-set-Nonunital-Precategory C)
      ( comp-hom-Nonunital-Precategory C)
```
