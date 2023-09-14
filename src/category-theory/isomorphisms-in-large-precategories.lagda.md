# Isomorphisms in large precategories

```agda
module category-theory.isomorphisms-in-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.large-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An isomorphism between objects `x y : A` in a precategory `C` is a morphism
`f : hom x y` for which there exists a morphism `g : hom y x` such that

- `G ∘ F = id_x` and
- `F ∘ G = id_y`.

## Definition

### The predicate of being an isomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : type-hom-Large-Precategory C X Y)
  where

  is-iso-hom-Large-Precategory : UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-hom-Large-Precategory =
    Σ ( type-hom-Large-Precategory C Y X)
      ( λ g →
        ( comp-hom-Large-Precategory C f g ＝ id-hom-Large-Precategory C) ×
        ( comp-hom-Large-Precategory C g f ＝ id-hom-Large-Precategory C))

  hom-inv-is-iso-hom-Large-Precategory :
    is-iso-hom-Large-Precategory → type-hom-Large-Precategory C Y X
  hom-inv-is-iso-hom-Large-Precategory = pr1

  is-section-hom-inv-is-iso-hom-Large-Precategory :
    (H : is-iso-hom-Large-Precategory) →
    comp-hom-Large-Precategory C f (hom-inv-is-iso-hom-Large-Precategory H) ＝
    id-hom-Large-Precategory C
  is-section-hom-inv-is-iso-hom-Large-Precategory = pr1 ∘ pr2

  is-retraction-hom-inv-is-iso-hom-Large-Precategory :
    (H : is-iso-hom-Large-Precategory) →
    comp-hom-Large-Precategory C (hom-inv-is-iso-hom-Large-Precategory H) f ＝
    id-hom-Large-Precategory C
  is-retraction-hom-inv-is-iso-hom-Large-Precategory = pr2 ∘ pr2
```

### Isomorphisms in a large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  where

  iso-Large-Precategory : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  iso-Large-Precategory =
    Σ (type-hom-Large-Precategory C X Y) (is-iso-hom-Large-Precategory C)

  hom-iso-Large-Precategory :
    iso-Large-Precategory → type-hom-Large-Precategory C X Y
  hom-iso-Large-Precategory = pr1

  is-iso-iso-Large-Precategory :
    (f : iso-Large-Precategory) →
    is-iso-hom-Large-Precategory C (hom-iso-Large-Precategory f)
  is-iso-iso-Large-Precategory f = pr2 f

  hom-inv-iso-Large-Precategory :
    iso-Large-Precategory → type-hom-Large-Precategory C Y X
  hom-inv-iso-Large-Precategory f = pr1 (pr2 f)

  is-section-hom-inv-iso-Large-Precategory :
    (f : iso-Large-Precategory) →
    ( comp-hom-Large-Precategory C
      ( hom-iso-Large-Precategory f)
      ( hom-inv-iso-Large-Precategory f)) ＝
    ( id-hom-Large-Precategory C)
  is-section-hom-inv-iso-Large-Precategory f = pr1 (pr2 (pr2 f))

  is-retraction-hom-inv-iso-Large-Precategory :
    (f : iso-Large-Precategory) →
    ( comp-hom-Large-Precategory C
      ( hom-inv-iso-Large-Precategory f)
      ( hom-iso-Large-Precategory f)) ＝
    ( id-hom-Large-Precategory C)
  is-retraction-hom-inv-iso-Large-Precategory f = pr2 (pr2 (pr2 f))
```

## Examples

### The identity morphisms are isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = id_x` (it is its own inverse).

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 : Level} {X : obj-Large-Precategory C l1}
  where

  is-iso-id-hom-Large-Precategory :
    is-iso-hom-Large-Precategory C (id-hom-Large-Precategory C {X = X})
  pr1 is-iso-id-hom-Large-Precategory = id-hom-Large-Precategory C
  pr1 (pr2 is-iso-id-hom-Large-Precategory) =
    left-unit-law-comp-hom-Large-Precategory C (id-hom-Large-Precategory C)
  pr2 (pr2 is-iso-id-hom-Large-Precategory) =
    left-unit-law-comp-hom-Large-Precategory C (id-hom-Large-Precategory C)

  id-iso-Large-Precategory : iso-Large-Precategory C X X
  pr1 id-iso-Large-Precategory = id-hom-Large-Precategory C
  pr2 id-iso-Large-Precategory = is-iso-id-hom-Large-Precategory
```

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because by the J-rule, it is enough to construct an isomorphism given
`refl : Id x x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
iso-eq-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precategory α β) {l1 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l1) →
  X ＝ Y → iso-Large-Precategory C X Y
iso-eq-Large-Precategory C X .X refl = id-iso-Large-Precategory C

compute-iso-eq-Large-Precategory :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precategory α β) {l1 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l1) →
  iso-eq-Precategory (precategory-Large-Precategory C l1) X Y ~
  iso-eq-Large-Precategory C X Y
compute-iso-eq-Large-Precategory C X .X refl = refl
```

## Properties

### Being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to
`f`. It is enough to show that `g = g'` since the equalities are propositions
(since the hom-types are sets). But we have the following chain of equalities:
`g = g ∘ id_y = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = id_x ∘ g' = g'`.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  where

  all-elements-equal-is-iso-hom-Large-Precategory :
    (f : type-hom-Large-Precategory C X Y)
    (H K : is-iso-hom-Large-Precategory C f) → H ＝ K
  all-elements-equal-is-iso-hom-Large-Precategory f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-type-subtype
      ( λ g →
        prod-Prop
          ( Id-Prop
            ( hom-Large-Precategory C Y Y)
            ( comp-hom-Large-Precategory C f g)
            ( id-hom-Large-Precategory C))
          ( Id-Prop
            ( hom-Large-Precategory C X X)
            ( comp-hom-Large-Precategory C g f)
            ( id-hom-Large-Precategory C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precategory C g)) ∙
        ( ( ap ( comp-hom-Large-Precategory C g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Large-Precategory C g f g')) ∙
            ( ( ap ( comp-hom-Large-Precategory' C g') q) ∙
              ( left-unit-law-comp-hom-Large-Precategory C g')))))

  is-prop-is-iso-hom-Large-Precategory :
    (f : type-hom-Large-Precategory C X Y) →
    is-prop (is-iso-hom-Large-Precategory C f)
  is-prop-is-iso-hom-Large-Precategory f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-iso-hom-Large-Precategory f)

  is-iso-prop-hom-Large-Precategory :
    (f : type-hom-Large-Precategory C X Y) → Prop (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 (is-iso-prop-hom-Large-Precategory f) =
    is-iso-hom-Large-Precategory C f
  pr2 (is-iso-prop-hom-Large-Precategory f) =
    is-prop-is-iso-hom-Large-Precategory f
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  where

  is-set-iso-Large-Precategory : is-set (iso-Large-Precategory C X Y)
  is-set-iso-Large-Precategory =
    is-set-type-subtype
      ( is-iso-prop-hom-Large-Precategory C X Y)
      ( is-set-type-hom-Large-Precategory C X Y)

  iso-Large-Precategory-Set : Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Large-Precategory-Set = iso-Large-Precategory C X Y
  pr2 iso-Large-Precategory-Set = is-set-iso-Large-Precategory
```

### Isomorphisms are stable by composition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  (Z : obj-Large-Precategory C l3)
  where

  is-iso-comp-iso-Large-Precategory :
    (g : type-hom-Large-Precategory C Y Z) →
    (f : type-hom-Large-Precategory C X Y) →
    is-iso-hom-Large-Precategory C g → is-iso-hom-Large-Precategory C f →
    is-iso-hom-Large-Precategory C (comp-hom-Large-Precategory C g f)
  pr1 (is-iso-comp-iso-Large-Precategory g f q p) =
    comp-hom-Large-Precategory C
      ( hom-inv-iso-Large-Precategory C X Y (pair f p))
      ( hom-inv-iso-Large-Precategory C Y Z (pair g q))
  pr1 (pr2 (is-iso-comp-iso-Large-Precategory g f q p)) =
    ( associative-comp-hom-Large-Precategory C g f
      ( pr1 (is-iso-comp-iso-Large-Precategory g f q p))) ∙
      ( ( ap
        ( comp-hom-Large-Precategory C g)
        ( ( inv
          ( associative-comp-hom-Large-Precategory C f
            ( hom-inv-iso-Large-Precategory C X Y (pair f p))
            ( hom-inv-iso-Large-Precategory C Y Z (pair g q)))) ∙
          ( ( ap
            ( λ h →
              comp-hom-Large-Precategory C h
                (hom-inv-iso-Large-Precategory C Y Z (pair g q)))
            ( is-section-hom-inv-iso-Large-Precategory C X Y (pair f p))) ∙
            ( left-unit-law-comp-hom-Large-Precategory C
              ( hom-inv-iso-Large-Precategory C Y Z (pair g q)))))) ∙
        ( is-section-hom-inv-iso-Large-Precategory C Y Z (pair g q)))
  pr2 (pr2 (is-iso-comp-iso-Large-Precategory g f q p)) =
    ( associative-comp-hom-Large-Precategory C
      ( hom-inv-iso-Large-Precategory C X Y (pair f p))
      ( hom-inv-iso-Large-Precategory C Y Z (pair g q))
      ( comp-hom-Large-Precategory C g f)) ∙
      ( ( ap
        ( comp-hom-Large-Precategory
          ( C)
          ( hom-inv-iso-Large-Precategory C X Y (pair f p)))
        ( ( inv
          ( associative-comp-hom-Large-Precategory C
            ( hom-inv-iso-Large-Precategory C Y Z (pair g q))
            ( g)
            ( f))) ∙
          ( ( ap
            ( λ h → comp-hom-Large-Precategory C h f)
            ( is-retraction-hom-inv-iso-Large-Precategory C Y Z (pair g q))) ∙
            ( left-unit-law-comp-hom-Large-Precategory C f)))) ∙
        ( is-retraction-hom-inv-iso-Large-Precategory C X Y (pair f p)))

  comp-iso-Large-Precategory :
    iso-Large-Precategory C Y Z →
    iso-Large-Precategory C X Y →
    iso-Large-Precategory C X Z
  pr1 (comp-iso-Large-Precategory g f) =
    comp-hom-Large-Precategory C
      ( hom-iso-Large-Precategory C Y Z g)
      ( hom-iso-Large-Precategory C X Y f)
  pr2 (comp-iso-Large-Precategory f g) =
    is-iso-comp-iso-Large-Precategory
      ( hom-iso-Large-Precategory C Y Z f)
      ( hom-iso-Large-Precategory C X Y g)
      ( is-iso-iso-Large-Precategory C Y Z f)
      ( is-iso-iso-Large-Precategory C X Y g)
```

### Isomorphisms are stable by inversion

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  where

  is-iso-inv-iso-Large-Precategory :
    (f : type-hom-Large-Precategory C X Y) →
    (p : is-iso-hom-Large-Precategory C f) →
    is-iso-hom-Large-Precategory C (hom-inv-iso-Large-Precategory C X Y (f , p))
  pr1 (is-iso-inv-iso-Large-Precategory f p) = f
  pr1 (pr2 (is-iso-inv-iso-Large-Precategory f p)) =
    is-retraction-hom-inv-iso-Large-Precategory C X Y (pair f p)
  pr2 (pr2 (is-iso-inv-iso-Large-Precategory f p)) =
    is-section-hom-inv-iso-Large-Precategory C X Y (pair f p)

  inv-iso-Large-Precategory :
    iso-Large-Precategory C X Y →
    iso-Large-Precategory C Y X
  pr1 (inv-iso-Large-Precategory f) = hom-inv-iso-Large-Precategory C X Y f
  pr2 (inv-iso-Large-Precategory f) =
    is-iso-inv-iso-Large-Precategory
      ( hom-iso-Large-Precategory C X Y f)
      ( is-iso-iso-Large-Precategory C X Y f)
```
