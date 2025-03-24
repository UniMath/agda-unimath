# Isomorphisms in subprecategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.isomorphisms-in-subprecategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations
open import category-theory.subprecategories funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels
```

</details>

## Definitions

### Isomorphisms in subprecategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  (f : hom-Subprecategory C P x y)
  where

  is-iso-prop-Subprecategory : Prop (l2 ⊔ l4)
  is-iso-prop-Subprecategory =
    is-iso-prop-Precategory (precategory-Subprecategory C P) {x} {y} f

  is-iso-Subprecategory : UU (l2 ⊔ l4)
  is-iso-Subprecategory = type-Prop is-iso-prop-Subprecategory

  is-prop-is-iso-Subprecategory : is-prop is-iso-Subprecategory
  is-prop-is-iso-Subprecategory = is-prop-type-Prop is-iso-prop-Subprecategory
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (x y : obj-Subprecategory C P)
  where

  iso-set-Subprecategory : Set (l2 ⊔ l4)
  iso-set-Subprecategory =
    iso-set-Precategory (precategory-Subprecategory C P) {x} {y}

  iso-Subprecategory : UU (l2 ⊔ l4)
  iso-Subprecategory = type-Set iso-set-Subprecategory

  is-set-iso-Subprecategory : is-set iso-Subprecategory
  is-set-iso-Subprecategory = is-set-type-Set iso-set-Subprecategory
```

#### The predicate on an isomorphism proof of being contained in a subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  (f : hom-Subprecategory C P x y)
  (is-iso-f : is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f))
  where

  is-in-is-iso-prop-Subprecategory : Prop l4
  is-in-is-iso-prop-Subprecategory =
    subtype-hom-obj-subprecategory-Subprecategory C P y x
      ( hom-inv-is-iso-Precategory C is-iso-f)

  is-in-is-iso-Subprecategory : UU l4
  is-in-is-iso-Subprecategory =
    type-Prop is-in-is-iso-prop-Subprecategory

  is-prop-is-in-is-iso-Subprecategory : is-prop is-in-is-iso-Subprecategory
  is-prop-is-in-is-iso-Subprecategory =
    is-prop-type-Prop is-in-is-iso-prop-Subprecategory

  is-iso-is-in-is-iso-Subprecategory :
    is-in-is-iso-Subprecategory → is-iso-Subprecategory C P f
  pr1 (pr1 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) =
    hom-inv-is-iso-Precategory C is-iso-f
  pr2 (pr1 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) =
    is-in-is-iso-f
  pr1 (pr2 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) =
    eq-type-subtype
      ( subtype-hom-obj-subprecategory-Subprecategory C P y y)
      ( pr1 (pr2 is-iso-f))
  pr2 (pr2 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) =
    eq-type-subtype
      ( subtype-hom-obj-subprecategory-Subprecategory C P x x)
      ( pr2 (pr2 is-iso-f))
```

#### The predicate on an isomorphism between objects in the subprecategory of being contained in the subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  (f :
    iso-Precategory C
      ( inclusion-obj-Subprecategory C P x)
      ( inclusion-obj-Subprecategory C P y))
  where

  is-in-iso-obj-subprecategory-prop-Subprecategory : Prop l4
  is-in-iso-obj-subprecategory-prop-Subprecategory =
    Σ-Prop
      ( subtype-hom-obj-subprecategory-Subprecategory C P x y
        ( hom-iso-Precategory C f))
      ( λ f₀ →
        is-in-is-iso-prop-Subprecategory C P
          ( hom-iso-Precategory C f , f₀)
          ( is-iso-iso-Precategory C f))

  is-in-iso-obj-subprecategory-Subprecategory : UU l4
  is-in-iso-obj-subprecategory-Subprecategory =
    type-Prop is-in-iso-obj-subprecategory-prop-Subprecategory

  is-prop-is-in-iso-obj-subprecategory-Subprecategory :
    is-prop is-in-iso-obj-subprecategory-Subprecategory
  is-prop-is-in-iso-obj-subprecategory-Subprecategory =
    is-prop-type-Prop is-in-iso-obj-subprecategory-prop-Subprecategory

  is-iso-is-in-iso-obj-subprecategory-Subprecategory :
    ((f₀ , f₁) : is-in-iso-obj-subprecategory-Subprecategory) →
    is-iso-Subprecategory C P (hom-iso-Precategory C f , f₀)
  is-iso-is-in-iso-obj-subprecategory-Subprecategory (f₀ , f₁) =
    is-iso-is-in-is-iso-Subprecategory C P (pr1 f , f₀) (pr2 f) f₁

  iso-is-in-iso-obj-subprecategory-Subprecategory :
    is-in-iso-obj-subprecategory-Subprecategory → iso-Subprecategory C P x y
  pr1 (pr1 (iso-is-in-iso-obj-subprecategory-Subprecategory is-in-iso-f)) =
    hom-iso-Precategory C f
  pr2 (pr1 (iso-is-in-iso-obj-subprecategory-Subprecategory is-in-iso-f)) =
    pr1 is-in-iso-f
  pr2 (iso-is-in-iso-obj-subprecategory-Subprecategory is-in-iso-f) =
    is-iso-is-in-is-iso-Subprecategory C P _
      ( is-iso-iso-Precategory C f)
      ( pr2 is-in-iso-f)
```

#### The predicate on an isomorphism between any objects of being contained in the subprecategory

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  is-in-iso-prop-Subprecategory : Prop (l3 ⊔ l4)
  is-in-iso-prop-Subprecategory =
    Σ-Prop
      ( subtype-obj-Subprecategory C P x)
      ( λ x₀ →
        Σ-Prop
          ( subtype-obj-Subprecategory C P y)
          ( λ y₀ →
            is-in-iso-obj-subprecategory-prop-Subprecategory C P
              { x , x₀} {y , y₀} f))

  is-in-iso-Subprecategory : UU (l3 ⊔ l4)
  is-in-iso-Subprecategory = type-Prop is-in-iso-prop-Subprecategory

  is-prop-is-in-iso-Subprecategory : is-prop is-in-iso-Subprecategory
  is-prop-is-in-iso-Subprecategory =
    is-prop-type-Prop is-in-iso-prop-Subprecategory

  iso-is-in-iso-Subprecategory :
    (is-in-iso-f : is-in-iso-Subprecategory) →
    iso-Subprecategory C P (x , pr1 is-in-iso-f) (y , pr1 (pr2 is-in-iso-f))
  iso-is-in-iso-Subprecategory is-in-iso-f =
    iso-is-in-iso-obj-subprecategory-Subprecategory C P f
      ( pr2 (pr2 is-in-iso-f))

  is-iso-is-in-iso-Subprecategory :
    ( is-in-iso-f : is-in-iso-Subprecategory) →
    is-iso-Subprecategory C P
      ( pr1 f , pr2 (pr1 (iso-is-in-iso-Subprecategory is-in-iso-f)))
  is-iso-is-in-iso-Subprecategory is-in-iso-f =
    pr2 (iso-is-in-iso-Subprecategory is-in-iso-f)
```

### If a subprecategory contains an object, it contains its identity ismorphism

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  (x : obj-Subprecategory C P)
  where

  is-iso-id-hom-Subprecategory :
    is-iso-Subprecategory C P (id-hom-Subprecategory C P {x})
  is-iso-id-hom-Subprecategory =
    is-iso-id-hom-Precategory (precategory-Subprecategory C P)

  is-in-is-iso-id-obj-subprecategory-Subprecategory :
    is-in-is-iso-Subprecategory C P {x}
      (id-hom-Subprecategory C P) (is-iso-id-hom-Precategory C)
  is-in-is-iso-id-obj-subprecategory-Subprecategory =
    contains-id-Subprecategory C P
      ( inclusion-obj-Subprecategory C P x)
      ( is-in-obj-inclusion-obj-Subprecategory C P x)

  is-in-iso-id-obj-subprecategory-Subprecategory :
    is-in-iso-obj-subprecategory-Subprecategory C P (id-iso-Precategory C)
  pr1 is-in-iso-id-obj-subprecategory-Subprecategory =
    is-in-is-iso-id-obj-subprecategory-Subprecategory
  pr2 is-in-iso-id-obj-subprecategory-Subprecategory =
    is-in-is-iso-id-obj-subprecategory-Subprecategory

  is-in-iso-id-Subprecategory :
    is-in-iso-Subprecategory C P (id-iso-Precategory C)
  pr1 is-in-iso-id-Subprecategory = is-in-obj-inclusion-obj-Subprecategory C P x
  pr1 (pr2 is-in-iso-id-Subprecategory) =
    is-in-obj-inclusion-obj-Subprecategory C P x
  pr2 (pr2 is-in-iso-id-Subprecategory) =
    is-in-iso-id-obj-subprecategory-Subprecategory
```

## Properties

### Isomorphisms in a subprecategory are isomorphisms in the base category

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (P : Subprecategory l3 l4 C)
  {x y : obj-Subprecategory C P}
  where

  is-iso-base-is-iso-Subprecategory :
    {f : hom-Subprecategory C P x y} →
    is-iso-Subprecategory C P f →
    is-iso-Precategory C (inclusion-hom-Subprecategory C P x y f)
  pr1 (is-iso-base-is-iso-Subprecategory is-iso-f) =
    pr1 (pr1 is-iso-f)
  pr1 (pr2 (is-iso-base-is-iso-Subprecategory is-iso-f)) =
    ap pr1 (pr1 (pr2 (is-iso-f)))
  pr2 (pr2 (is-iso-base-is-iso-Subprecategory is-iso-f)) =
    ap pr1 (pr2 (pr2 (is-iso-f)))
```
