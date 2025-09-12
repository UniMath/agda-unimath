# Replete subprecategories

```agda
module category-theory.replete-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphism-induction-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.isomorphisms-in-subprecategories
open import category-theory.precategories
open import category-theory.subprecategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subsingleton-induction
open import foundation.subtypes
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **replete subprecategory** of a [precategory](category-theory.categories.md)
`C` is a [subprecategory](category-theory.subprecategories.md) `P` that is
closed under [isomorphisms](category-theory.isomorphisms-in-precategories.md):

Given an object `x` in `P`, then every isomorphism `f : x ≅ y` in `C`, is
contained in `P`.

## Definitions

### The predicate on a subprecategory of being closed under isomorphic objects

We can define what it means for subprecategories to have objects that are closed
under isomorphisms. Observe that this is not yet the correct definition of a
replete subprecategory.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  contains-iso-obj-Subprecategory : UU (l1 ⊔ l2 ⊔ l3)
  contains-iso-obj-Subprecategory =
    (x : obj-Subprecategory C P) (y : obj-Precategory C) →
    iso-Precategory C (inclusion-obj-Subprecategory C P x) y →
    is-in-obj-Subprecategory C P y

  is-prop-contains-iso-obj-Subprecategory :
    is-prop contains-iso-obj-Subprecategory
  is-prop-contains-iso-obj-Subprecategory =
    is-prop-iterated-Π 3 (λ x y f → is-prop-is-in-obj-Subprecategory C P y)

  contains-iso-obj-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 contains-iso-obj-prop-Subprecategory = contains-iso-obj-Subprecategory
  pr2 contains-iso-obj-prop-Subprecategory =
    is-prop-contains-iso-obj-Subprecategory
```

### The predicate of being a replete subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-replete-Subprecategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-replete-Subprecategory =
    (x : obj-Subprecategory C P)
    (y : obj-Precategory C)
    (f : iso-Precategory C (inclusion-obj-Subprecategory C P x) y) →
    Σ ( is-in-obj-Subprecategory C P y)
      ( λ y₀ → is-in-iso-obj-subprecategory-Subprecategory C P {x} {y , y₀} f)

  is-prop-is-replete-Subprecategory :
    is-prop is-replete-Subprecategory
  is-prop-is-replete-Subprecategory =
    is-prop-iterated-Π 3
      ( λ x y f →
        is-prop-Σ
          ( is-prop-is-in-obj-Subprecategory C P y)
          ( λ _ → is-prop-is-in-iso-obj-subprecategory-Subprecategory C P f))

  is-replete-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-replete-prop-Subprecategory = is-replete-Subprecategory
  pr2 is-replete-prop-Subprecategory =
    is-prop-is-replete-Subprecategory
```

### The type of replete subprecategories

```agda
Replete-Subprecategory :
  {l1 l2 : Level} (l3 l4 : Level) (C : Precategory l1 l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Replete-Subprecategory l3 l4 C =
  Σ (Subprecategory l3 l4 C) (is-replete-Subprecategory C)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Replete-Subprecategory l3 l4 C)
  where

  subprecategory-Replete-Subprecategory : Subprecategory l3 l4 C
  subprecategory-Replete-Subprecategory = pr1 P

  is-replete-Replete-Subprecategory :
    is-replete-Subprecategory C subprecategory-Replete-Subprecategory
  is-replete-Replete-Subprecategory = pr2 P
```

## Properties

### A slight reformulation of repleteness

In our main definition of repleteness, the containment proof of the isomorphism
must be fixed at the left end-point. This is of course not necessary, so we can
ask for a slightly relaxed proof of repleteness:

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  where

  is-unfixed-replete-Subprecategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-unfixed-replete-Subprecategory =
    (x : obj-Subprecategory C P)
    (y : obj-Precategory C)
    (f : iso-Precategory C (inclusion-obj-Subprecategory C P x) y) →
    is-in-iso-Subprecategory C P f

  is-prop-is-unfixed-replete-Subprecategory :
    is-prop (is-unfixed-replete-Subprecategory)
  is-prop-is-unfixed-replete-Subprecategory =
    is-prop-iterated-Π 3
      ( λ x y f → is-prop-is-in-iso-Subprecategory C P f)

  is-unfixed-replete-prop-Subprecategory : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-unfixed-replete-prop-Subprecategory =
    is-unfixed-replete-Subprecategory
  pr2 is-unfixed-replete-prop-Subprecategory =
    is-prop-is-unfixed-replete-Subprecategory

  is-unfixed-replete-is-replete-Subprecategory :
    is-replete-Subprecategory C P → is-unfixed-replete-Subprecategory
  pr1 (is-unfixed-replete-is-replete-Subprecategory replete' (x , x₀) y f) = x₀
  pr2 (is-unfixed-replete-is-replete-Subprecategory replete' x y f) =
    replete' x y f

  is-replete-is-unfixed-replete-Subprecategory :
    is-unfixed-replete-Subprecategory → is-replete-Subprecategory C P
  is-replete-is-unfixed-replete-Subprecategory is-unfixed-replete-P x y f =
    ind-subsingleton
      ( is-prop-is-in-obj-Subprecategory C P (pr1 x))
      { λ x₀ →
        Σ ( is-in-obj-Subprecategory C P y)
          ( λ y₀ →
            is-in-iso-obj-subprecategory-Subprecategory C P
              { inclusion-obj-Subprecategory C P x , x₀} {y , y₀} f)}
      ( pr1 (is-unfixed-replete-P x y f))
      ( pr2 (is-unfixed-replete-P x y f))
      ( is-in-obj-inclusion-obj-Subprecategory C P x)
```

### Isomorphism-sets in replete subprecategories are equivalent to isomorphism-sets in the base precategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (is-replete-P : is-replete-Subprecategory C P)
  {x y : obj-Subprecategory C P} (f : hom-Subprecategory C P x y)
  where

  is-iso-is-iso-base-is-replete-Subprecategory :
    is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f) →
    is-iso-Subprecategory C P f
  pr1 (pr1 (is-iso-is-iso-base-is-replete-Subprecategory is-iso-C-f)) =
    hom-inv-is-iso-Precategory C is-iso-C-f
  pr2 (pr1 (is-iso-is-iso-base-is-replete-Subprecategory is-iso-C-f)) =
    ind-subsingleton
      ( is-prop-is-in-obj-Subprecategory C P (pr1 y))
      { λ y₀ →
        is-in-hom-obj-subprecategory-Subprecategory C P (pr1 y , y₀) x
          ( hom-inv-is-iso-Precategory C is-iso-C-f)}
      ( pr1 (is-replete-P x (pr1 y) (pr1 f , is-iso-C-f)))
      ( pr2 (pr2 (is-replete-P x (pr1 y) (pr1 f , is-iso-C-f))))
      ( pr2 y)
  pr1 (pr2 (is-iso-is-iso-base-is-replete-Subprecategory is-iso-C-f)) =
    eq-type-subtype
      ( subtype-hom-obj-subprecategory-Subprecategory C P y y)
      ( is-section-hom-inv-is-iso-Precategory C is-iso-C-f)
  pr2 (pr2 (is-iso-is-iso-base-is-replete-Subprecategory is-iso-C-f)) =
    eq-type-subtype
      ( subtype-hom-obj-subprecategory-Subprecategory C P x x)
      ( is-retraction-hom-inv-is-iso-Precategory C is-iso-C-f)

  is-equiv-is-iso-is-iso-base-is-replete-Subprecategory :
    is-equiv is-iso-is-iso-base-is-replete-Subprecategory
  is-equiv-is-iso-is-iso-base-is-replete-Subprecategory =
    is-equiv-has-converse-is-prop
      ( is-prop-is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f))
      ( is-prop-is-iso-Subprecategory C P f)
      ( is-iso-base-is-iso-Subprecategory C P)

  equiv-is-iso-is-iso-base-is-replete-Subprecategory :
    is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f) ≃
    is-iso-Subprecategory C P f
  pr1 equiv-is-iso-is-iso-base-is-replete-Subprecategory =
    is-iso-is-iso-base-is-replete-Subprecategory
  pr2 equiv-is-iso-is-iso-base-is-replete-Subprecategory =
    is-equiv-is-iso-is-iso-base-is-replete-Subprecategory

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (is-replete-P : is-replete-Subprecategory C P)
  (x y : obj-Subprecategory C P)
  where

  compute-iso-is-replete-Subprecategory :
    iso-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y) ≃
    iso-Subprecategory C P x y
  compute-iso-is-replete-Subprecategory =
    ( equiv-tot
      ( equiv-is-iso-is-iso-base-is-replete-Subprecategory
          C P is-replete-P {x} {y})) ∘e
    ( inv-associative-Σ) ∘e
    ( equiv-tot
      ( λ f →
        ( commutative-product) ∘e
        ( inv-right-unit-law-Σ-is-contr
          ( λ is-iso-C-f → is-proof-irrelevant-is-prop
            ( is-prop-is-in-hom-obj-subprecategory-Subprecategory C P x y f)
            ( ind-subsingleton
              ( is-prop-is-in-obj-Subprecategory C P (pr1 y))
              { λ y₀ →
                is-in-hom-obj-subprecategory-Subprecategory
                  C P x (pr1 y , y₀) f}
              ( is-replete-P x (pr1 y) (f , is-iso-C-f) .pr1)
              ( is-replete-P x (pr1 y) (f , is-iso-C-f) .pr2 .pr1)
              ( pr2 y))))))

  inv-compute-iso-is-replete-Subprecategory :
    iso-Subprecategory C P x y ≃
    iso-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y)
  inv-compute-iso-is-replete-Subprecategory =
    inv-equiv compute-iso-is-replete-Subprecategory
```

### Subprecategories of categories are replete

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (is-category-C : is-category-Precategory C)
  where

  is-unfixed-replete-subprecategory-is-category-Subprecategory :
    {x : obj-Subprecategory C P}
    {y : obj-Precategory C}
    (f : iso-Precategory C (inclusion-obj-Subprecategory C P x) y) →
    is-in-iso-Subprecategory C P f
  is-unfixed-replete-subprecategory-is-category-Subprecategory {x} =
    ind-iso-Category
      ( C , is-category-C)
      ( λ B → is-in-iso-Subprecategory C P)
      ( is-in-iso-id-Subprecategory C P x)

  is-replete-subprecategory-is-category-Subprecategory :
    is-replete-Subprecategory C P
  is-replete-subprecategory-is-category-Subprecategory x y =
    ind-iso-Category
      ( C , is-category-C)
      ( λ z e →
        Σ ( is-in-obj-Subprecategory C P z)
          ( λ z₀ →
            is-in-iso-obj-subprecategory-Subprecategory C P {x} {z , z₀} e))
      ( pr2 (is-in-iso-id-Subprecategory C P x))
```

### If a full subprecategory is closed under isomorphic objects then it is replete

This remains to be formalized.

### The inclusion functor of a replete subprecategory is pseudomonic

This remains to be formalized.

## See also

- Every [subcategory](category-theory.subcategories.md) is replete.
- Because of universe polymorphism,
  [large subcategories](category-theory.large-subcategories.md) are not large
  replete by construction, although they are levelwise replete.

## External links

- [replete subcategory](https://ncatlab.org/nlab/show/replete+replete-subprecategory)
  at $n$Lab
- [Isomorphism-closed subcategory](https://en.wikipedia.org/wiki/Isomorphism-closed_subcategory)
  at Wikipedia
- [isomorphism-closed subcategory](https://www.wikidata.org/wiki/Q6086096) at
  Wikidata
