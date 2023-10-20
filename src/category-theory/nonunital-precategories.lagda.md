# Nonunital precategories

```agda
module category-theory.nonunital-precategories where

open import category-theory.composition-operations-on-binary-families-of-sets public
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets

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

### Nonunital precategories

```agda
Nonunital-Precategory :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Nonunital-Precategory l1 l2 =
  Σ ( UU l1)
    ( λ A →
      Σ ( A → A → Set l2)
        ( associative-composition-operation-binary-family-Set))

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

  associative-composition-operation-Nonunital-Precategory :
    associative-composition-operation-binary-family-Set
      hom-set-Nonunital-Precategory
  associative-composition-operation-Nonunital-Precategory = pr2 (pr2 C)

  comp-hom-Nonunital-Precategory :
    {x y z : obj-Nonunital-Precategory} →
    hom-Nonunital-Precategory y z →
    hom-Nonunital-Precategory x y →
    hom-Nonunital-Precategory x z
  comp-hom-Nonunital-Precategory =
    pr1 associative-composition-operation-Nonunital-Precategory

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
    pr2 associative-composition-operation-Nonunital-Precategory
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
  (f : hom-Nonunital-Precategory C x y)
  (z : obj-Nonunital-Precategory C) →
  hom-Nonunital-Precategory C y z → hom-Nonunital-Precategory C x z
precomp-hom-Nonunital-Precategory C f z g =
  comp-hom-Nonunital-Precategory C g f
```

### Postcomposition by a morphism

```agda
postcomp-hom-Nonunital-Precategory :
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  {x y : obj-Nonunital-Precategory C}
  (f : hom-Nonunital-Precategory C x y)
  (z : obj-Nonunital-Precategory C) →
  hom-Nonunital-Precategory C z x → hom-Nonunital-Precategory C z y
postcomp-hom-Nonunital-Precategory C f z =
  comp-hom-Nonunital-Precategory C f
```

### The predicate of being unital on nonunital precategories

Suppose `e e' : (x : A) → hom-set x x` are both right and left units with regard
to composition. It is enough to show that `e = e'` since the right and left unit
laws are propositions (because all hom-types are sets). By function
extensionality, it is enough to show that `e x = e' x` for all `x : A`. But by
the unit laws we have the following chain of equalities:
`e x = (e' x) ∘ (e x) = e' x.`

```agda
module _
  {l1 l2 : Level} (C : Nonunital-Precategory l1 l2)
  where

  is-unital-Nonunital-Precategory : UU (l1 ⊔ l2)
  is-unital-Nonunital-Precategory =
    is-unital-composition-operation-binary-family-Set
      ( hom-set-Nonunital-Precategory C)
      ( comp-hom-Nonunital-Precategory C)

  is-prop-is-unital-Nonunital-Precategory :
    is-prop
      ( is-unital-composition-operation-binary-family-Set
        ( hom-set-Nonunital-Precategory C)
        ( comp-hom-Nonunital-Precategory C))
  is-prop-is-unital-Nonunital-Precategory =
    is-prop-is-unital-composition-operation-binary-family-Set
      ( hom-set-Nonunital-Precategory C)
      ( comp-hom-Nonunital-Precategory C)

  is-unital-prop-Nonunital-Precategory : Prop (l1 ⊔ l2)
  is-unital-prop-Nonunital-Precategory =
    is-unital-prop-composition-operation-binary-family-Set
      ( hom-set-Nonunital-Precategory C)
      ( comp-hom-Nonunital-Precategory C)
```

## Comments

As discussed in [Semicategories](https://ncatlab.org/nlab/show/semicategory) at
nlab, it seems that a nonunital precategory should be the underlying nonunital
precategory of a [category](category-theory.categories.md) if and only if the
projection map

```text
  pr1 : (Σ (a : A) Σ (f : hom a a) (is-neutral f)) → A
```

is an [equivalence](foundation-core.equivalences.md).

We can also define a notion of "isomorphism" as those that induce equivalences
of hom-sets by pre- and postcomposition.
