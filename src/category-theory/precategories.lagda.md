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
open import foundation.strictly-involutive-identity-types
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "precategory" Agda=Precategory}} `𝒞` in Homotopy Type Theory is the
structure of an associative and unital
[composition operation](category-theory.composition-operations-on-binary-families-of-sets.md)
on a binary familiy of sets.

This means a precategory consists of:

- **Objects.** A type `Ob 𝒞` of _objects_.
- **Morphisms.** For each pair of objects `x y : Ob 𝒞`, a
  [set](foundation-core.sets.md) of _morphisms_ `hom 𝒞 x y : Set`.
- **Composition.** For every triple of objects `x y z : Ob 𝒞` there is a
  _composition operation_ on morphisms
  ```text
    _∘_ : hom 𝒞 y z → hom 𝒞 x y → hom 𝒞 x z.
  ```
- **Associativity.** For every triple of composable morphisms, we have
  ```text
    (h ∘ g) ∘ f ＝ h ∘ (g ∘ f).
  ```
- **Identity morphisms.** For every object `x : Ob 𝒞`, there is a distinguished
  _identity_ morphism `id_x : hom 𝒞 x x`.
- **Unitality.** The identity morphisms are two-sided units for the composition
  operation, meaning that for every `f : hom 𝒞 x y` we have
  ```text
    id_y ∘ f ＝ f   and   f ∘ id_x ＝ f.
  ```

**Note.** The reason this is called a *pre*category and not a _category_ in
Homotopy Type Theory is that we reserve that name for precategories where the
[identity types](foundation-core.identity-types.md) of the type of objects are
characterized by the
[isomorphism sets](category-theory.isomorphisms-in-precategories.md).

## Definitions

### The predicate on composition operations on binary families of sets of being a precategory

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  (hom-set : A → A → Set l2)
  (comp-hom : composition-operation-binary-family-Set hom-set)
  where

  is-precategory-prop-composition-operation-binary-family-Set : Prop (l1 ⊔ l2)
  is-precategory-prop-composition-operation-binary-family-Set =
    product-Prop
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

make-Precategory :
  { l1 l2 : Level}
  ( obj : UU l1)
  ( hom-set : obj → obj → Set l2)
  ( _∘_ : composition-operation-binary-family-Set hom-set)
  ( id : (x : obj) → type-Set (hom-set x x))
  ( assoc-comp-hom :
    { x y z w : obj} →
    ( h : type-Set (hom-set z w))
    ( g : type-Set (hom-set y z))
    ( f : type-Set (hom-set x y)) →
    ( (h ∘ g) ∘ f ＝ h ∘ (g ∘ f)))
  ( left-unit-comp-hom :
    { x y : obj} (f : type-Set (hom-set x y)) → id y ∘ f ＝ f)
  ( right-unit-comp-hom :
    { x y : obj} (f : type-Set (hom-set x y)) → f ∘ id x ＝ f) →
  Precategory l1 l2
make-Precategory
  obj hom-set _∘_ id assoc-comp-hom left-unit-comp-hom right-unit-comp-hom =
  ( ( obj) ,
    ( hom-set) ,
    ( _∘_ , (λ h g f → involutive-eq-eq (assoc-comp-hom h g f))) ,
    ( id) ,
    ( left-unit-comp-hom) ,
    ( right-unit-comp-hom))

{-# INLINE make-Precategory #-}

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

  involutive-eq-associative-comp-hom-Precategory :
    {x y z w : obj-Precategory}
    (h : hom-Precategory z w)
    (g : hom-Precategory y z)
    (f : hom-Precategory x y) →
    ( comp-hom-Precategory (comp-hom-Precategory h g) f) ＝ⁱ
    ( comp-hom-Precategory h (comp-hom-Precategory g f))
  involutive-eq-associative-comp-hom-Precategory =
    involutive-eq-associative-composition-operation-binary-family-Set
      ( hom-set-Precategory)
      ( associative-composition-operation-Precategory)

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

### If the objects of a precategory are `k`-truncated for nonnegative `k`, the total hom-type is `k`-truncated

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
- [Functors between precategories](category-theory.functors-precategories.md)
  are [structure](foundation.structure.md)-preserving maps of precategories.
- [Large precategories](category-theory.large-precategories.md) are
  precategories whose collections of objects and morphisms form large types.

## External links

- [Precategories](https://1lab.dev/Cat.Base.html) at 1lab
- [precategory](https://ncatlab.org/nlab/show/precategory) at $n$Lab
