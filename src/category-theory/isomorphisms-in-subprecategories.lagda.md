# Isomorphisms in subprecategories

```agda
module category-theory.isomorphisms-in-subprecategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphism-induction-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.subprecategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subsingleton-induction
open import foundation.subtypes
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
  where

  is-iso-Subprecategory :
    {x y : obj-Subprecategory C P} → hom-Subprecategory C P x y → UU (l2 ⊔ l4)
  is-iso-Subprecategory {x} {y} =
    is-iso-Precategory (precategory-Subprecategory C P) {x} {y}

  iso-Subprecategory :
    (x y : obj-Subprecategory C P) → UU (l2 ⊔ l4)
  iso-Subprecategory = iso-Precategory (precategory-Subprecategory C P)
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
    subhom-subobj-Subprecategory C P y x (hom-inv-is-iso-Precategory C is-iso-f)

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
  pr2 (pr1 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) = is-in-is-iso-f
  pr1 (pr2 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) =
    eq-type-subtype (subhom-subobj-Subprecategory C P y y) (pr1 (pr2 is-iso-f))
  pr2 (pr2 (is-iso-is-in-is-iso-Subprecategory is-in-is-iso-f)) =
    eq-type-subtype (subhom-subobj-Subprecategory C P x x) (pr2 (pr2 is-iso-f))
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

  is-in-iso-subobj-prop-Subprecategory : Prop l4
  is-in-iso-subobj-prop-Subprecategory =
    Σ-Prop
      ( subhom-subobj-Subprecategory C P x y (hom-iso-Precategory C f))
      ( λ f₀ →
        is-in-is-iso-prop-Subprecategory C P
          ( hom-iso-Precategory C f , f₀)
          ( is-iso-iso-Precategory C f))

  is-in-iso-subobj-Subprecategory : UU l4
  is-in-iso-subobj-Subprecategory =
    type-Prop is-in-iso-subobj-prop-Subprecategory

  is-prop-is-in-iso-subobj-Subprecategory :
    is-prop is-in-iso-subobj-Subprecategory
  is-prop-is-in-iso-subobj-Subprecategory =
    is-prop-type-Prop is-in-iso-subobj-prop-Subprecategory

  iso-is-in-iso-subobj-Subprecategory :
    is-in-iso-subobj-Subprecategory → iso-Subprecategory C P x y
  pr1 (pr1 (iso-is-in-iso-subobj-Subprecategory is-in-iso-f)) =
    hom-iso-Precategory C f
  pr2 (pr1 (iso-is-in-iso-subobj-Subprecategory is-in-iso-f)) =
    pr1 is-in-iso-f
  pr2 (iso-is-in-iso-subobj-Subprecategory is-in-iso-f) =
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
      ( subobj-Subprecategory C P x)
      ( λ x₀ →
        Σ-Prop
          ( subobj-Subprecategory C P y)
          ( λ y₀ →
            is-in-iso-subobj-prop-Subprecategory C P {x , x₀} {y , y₀} f))

  is-in-iso-Subprecategory : UU (l3 ⊔ l4)
  is-in-iso-Subprecategory = type-Prop is-in-iso-prop-Subprecategory

  is-prop-is-in-iso-Subprecategory : is-prop is-in-iso-Subprecategory
  is-prop-is-in-iso-Subprecategory =
    is-prop-type-Prop is-in-iso-prop-Subprecategory

  iso-is-in-iso-Subprecategory :
    (is-in-iso-f : is-in-iso-Subprecategory) →
    iso-Subprecategory C P (x , pr1 is-in-iso-f) (y , pr1 (pr2 is-in-iso-f))
  iso-is-in-iso-Subprecategory is-in-iso-f =
    iso-is-in-iso-subobj-Subprecategory C P f (pr2 (pr2 is-in-iso-f))
```
