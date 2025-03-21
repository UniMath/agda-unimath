# Pregroupoids

```agda
module category-theory.pregroupoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.telescopes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **pregroupoid** is a [precategory](category-theory.precategories.md) in which
every morphism is an
[isomorphism](category-theory.isomorphisms-in-precategories.md).

## Definitions

### The predicate on precategories of being a pregroupoid

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-pregroupoid-Precategory : UU (l1 ⊔ l2)
  is-pregroupoid-Precategory =
    (x y : obj-Precategory C) (f : hom-Precategory C x y) →
    is-iso-Precategory C f

  is-prop-is-pregroupoid-Precategory : is-prop is-pregroupoid-Precategory
  is-prop-is-pregroupoid-Precategory =
    is-prop-iterated-Π 3 (λ x y → is-prop-is-iso-Precategory C)

  is-pregroupoid-prop-Precategory : Prop (l1 ⊔ l2)
  pr1 is-pregroupoid-prop-Precategory = is-pregroupoid-Precategory
  pr2 is-pregroupoid-prop-Precategory = is-prop-is-pregroupoid-Precategory
```

### The type of pregroupoids

```agda
Pregroupoid :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pregroupoid l1 l2 = Σ (Precategory l1 l2) (is-pregroupoid-Precategory)

module _
  {l1 l2 : Level} (G : Pregroupoid l1 l2)
  where

  precategory-Pregroupoid : Precategory l1 l2
  precategory-Pregroupoid = pr1 G

  is-pregroupoid-Pregroupoid :
    is-pregroupoid-Precategory precategory-Pregroupoid
  is-pregroupoid-Pregroupoid = pr2 G

  obj-Pregroupoid : UU l1
  obj-Pregroupoid = obj-Precategory precategory-Pregroupoid

  hom-set-Pregroupoid : obj-Pregroupoid → obj-Pregroupoid → Set l2
  hom-set-Pregroupoid = hom-set-Precategory precategory-Pregroupoid

  hom-Pregroupoid : obj-Pregroupoid → obj-Pregroupoid → UU l2
  hom-Pregroupoid = hom-Precategory precategory-Pregroupoid

  id-hom-Pregroupoid :
    {x : obj-Pregroupoid} → hom-Pregroupoid x x
  id-hom-Pregroupoid = id-hom-Precategory precategory-Pregroupoid

  comp-hom-Pregroupoid :
    {x y z : obj-Pregroupoid} → hom-Pregroupoid y z →
    hom-Pregroupoid x y → hom-Pregroupoid x z
  comp-hom-Pregroupoid = comp-hom-Precategory precategory-Pregroupoid

  associative-comp-hom-Pregroupoid :
    {x y z w : obj-Pregroupoid} (h : hom-Pregroupoid z w)
    (g : hom-Pregroupoid y z) (f : hom-Pregroupoid x y) →
    comp-hom-Pregroupoid (comp-hom-Pregroupoid h g) f ＝
    comp-hom-Pregroupoid h (comp-hom-Pregroupoid g f)
  associative-comp-hom-Pregroupoid =
    associative-comp-hom-Precategory precategory-Pregroupoid

  involutive-eq-associative-comp-hom-Pregroupoid :
    {x y z w : obj-Pregroupoid} (h : hom-Pregroupoid z w)
    (g : hom-Pregroupoid y z) (f : hom-Pregroupoid x y) →
    comp-hom-Pregroupoid (comp-hom-Pregroupoid h g) f ＝ⁱ
    comp-hom-Pregroupoid h (comp-hom-Pregroupoid g f)
  involutive-eq-associative-comp-hom-Pregroupoid =
    involutive-eq-associative-comp-hom-Precategory precategory-Pregroupoid

  left-unit-law-comp-hom-Pregroupoid :
    {x y : obj-Pregroupoid} (f : hom-Pregroupoid x y) →
    ( comp-hom-Pregroupoid id-hom-Pregroupoid f) ＝ f
  left-unit-law-comp-hom-Pregroupoid =
    left-unit-law-comp-hom-Precategory precategory-Pregroupoid

  right-unit-law-comp-hom-Pregroupoid :
    {x y : obj-Pregroupoid} (f : hom-Pregroupoid x y) →
    ( comp-hom-Pregroupoid f id-hom-Pregroupoid) ＝ f
  right-unit-law-comp-hom-Pregroupoid =
    right-unit-law-comp-hom-Precategory precategory-Pregroupoid

  iso-Pregroupoid : (x y : obj-Pregroupoid) → UU l2
  iso-Pregroupoid = iso-Precategory precategory-Pregroupoid
```

## Properties

### The type of isomorphisms in a pregroupoid is equivalent to the type of morphisms

```agda
module _
  {l1 l2 : Level} (G : Pregroupoid l1 l2)
  where

  inv-compute-iso-Pregroupoid :
    {x y : obj-Pregroupoid G} → iso-Pregroupoid G x y ≃ hom-Pregroupoid G x y
  inv-compute-iso-Pregroupoid {x} {y} =
    right-unit-law-Σ-is-contr
      ( λ f →
        is-proof-irrelevant-is-prop
          ( is-prop-is-iso-Precategory (precategory-Pregroupoid G) f)
          ( is-pregroupoid-Pregroupoid G x y f))

  compute-iso-Pregroupoid :
    {x y : obj-Pregroupoid G} → hom-Pregroupoid G x y ≃ iso-Pregroupoid G x y
  compute-iso-Pregroupoid = inv-equiv inv-compute-iso-Pregroupoid
```

## See also

- [Cores of precategories](category-theory.cores-precategories.md)

## External links

- [Groupoids](https://1lab.dev/Cat.Groupoid.html) at 1lab
- [pregroupoid](https://ncatlab.org/nlab/show/pregroupoid) at $n$Lab
