# Isomorphisms in large categories

```agda
module category-theory.isomorphisms-in-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-categories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

An **isomorphism** in a [large category](category-theory.large-categories.md)
`C` is a morphism `f : X → Y` in `C` for which there exists a morphism
`g : Y → X` such that `f ∘ g ＝ id` and `g ∘ f ＝ id`.

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  (f : hom-Large-Category C X Y)
  where

  is-iso-Large-Category : UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-Large-Category =
    is-iso-Large-Precategory (large-precategory-Large-Category C) f

  hom-inv-is-iso-Large-Category :
    is-iso-Large-Category → hom-Large-Category C Y X
  hom-inv-is-iso-Large-Category =
    hom-inv-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)

  is-section-hom-inv-is-iso-Large-Category :
    (H : is-iso-Large-Category) →
    comp-hom-Large-Category C f (hom-inv-is-iso-Large-Category H) ＝
    id-hom-Large-Category C
  is-section-hom-inv-is-iso-Large-Category =
    is-section-hom-inv-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)

  is-retraction-hom-inv-is-iso-Large-Category :
    (H : is-iso-Large-Category) →
    comp-hom-Large-Category C (hom-inv-is-iso-Large-Category H) f ＝
    id-hom-Large-Category C
  is-retraction-hom-inv-is-iso-Large-Category =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)
```

### Isomorphisms in a large category

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  (X : obj-Large-Category C l1) (Y : obj-Large-Category C l2)
  where

  iso-Large-Category : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  iso-Large-Category =
    iso-Large-Precategory (large-precategory-Large-Category C) X Y

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  (f : iso-Large-Category C X Y)
  where

  hom-iso-Large-Category : hom-Large-Category C X Y
  hom-iso-Large-Category =
    hom-iso-Large-Precategory (large-precategory-Large-Category C) f

  is-iso-iso-Large-Category :
    is-iso-Large-Category C hom-iso-Large-Category
  is-iso-iso-Large-Category =
    is-iso-iso-Large-Precategory (large-precategory-Large-Category C) f

  hom-inv-iso-Large-Category : hom-Large-Category C Y X
  hom-inv-iso-Large-Category =
    hom-inv-iso-Large-Precategory (large-precategory-Large-Category C) f

  is-section-hom-inv-iso-Large-Category :
    ( comp-hom-Large-Category C
      ( hom-iso-Large-Category)
      ( hom-inv-iso-Large-Category)) ＝
    ( id-hom-Large-Category C)
  is-section-hom-inv-iso-Large-Category =
    is-section-hom-inv-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)

  is-retraction-hom-inv-iso-Large-Category :
    ( comp-hom-Large-Category C
      ( hom-inv-iso-Large-Category)
      ( hom-iso-Large-Category)) ＝
    ( id-hom-Large-Category C)
  is-retraction-hom-inv-iso-Large-Category =
    is-retraction-hom-inv-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)
```

## Examples

### The identity isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = id_x` (it is its own inverse).

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 : Level} {X : obj-Large-Category C l1}
  where

  is-iso-id-hom-Large-Category :
    is-iso-Large-Category C (id-hom-Large-Category C {X = X})
  is-iso-id-hom-Large-Category =
    is-iso-id-hom-Large-Precategory (large-precategory-Large-Category C)

  id-iso-Large-Category : iso-Large-Category C X X
  id-iso-Large-Category =
    id-iso-Large-Precategory (large-precategory-Large-Category C)
```

### Equalities induce isomorphisms

An equality between objects `X Y : A` gives rise to an isomorphism between them.
This is because, by the J-rule, it is enough to construct an isomorphism given
`refl : X ＝ X`, from `X` to itself. We take the identity morphism as such an
isomorphism.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 : Level}
  (X Y : obj-Large-Category C l1)
  where

  iso-eq-Large-Category :
    X ＝ Y → iso-Large-Category C X Y
  iso-eq-Large-Category =
    iso-eq-Large-Precategory (large-precategory-Large-Category C) X Y

  eq-iso-Large-Category :
    iso-Large-Category C X Y → X ＝ Y
  eq-iso-Large-Category =
    map-inv-is-equiv (is-large-category-Large-Category C X Y)

  compute-iso-eq-Large-Category :
    iso-eq-Category (category-Large-Category C l1) X Y ~
    iso-eq-Large-Category
  compute-iso-eq-Large-Category =
    compute-iso-eq-Large-Precategory (large-precategory-Large-Category C) X Y

  extensionality-obj-Large-Category :
    (X ＝ Y) ≃ iso-Large-Category C X Y
  pr1 extensionality-obj-Large-Category =
    iso-eq-Large-Category
  pr2 extensionality-obj-Large-Category =
    is-large-category-Large-Category C X Y

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 : Level}
  (X : obj-Large-Category C l1)
  where

  is-torsorial-iso-Large-Category :
    is-torsorial (iso-Large-Category C X)
  is-torsorial-iso-Large-Category =
    is-contr-equiv'
      ( Σ (obj-Large-Category C l1) (X ＝_))
      ( equiv-tot (extensionality-obj-Large-Category C X))
      ( is-torsorial-Id X)

  is-torsorial-iso-Large-Category' :
    is-torsorial (λ Y → iso-Large-Category C Y X)
  is-torsorial-iso-Large-Category' =
    is-contr-equiv'
      ( Σ (obj-Large-Category C l1) (_＝ X))
      ( equiv-tot (λ Y → extensionality-obj-Large-Category C Y X))
      ( is-torsorial-Id' X)
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
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  where

  all-elements-equal-is-iso-Large-Category :
    (f : hom-Large-Category C X Y)
    (H K : is-iso-Large-Category C f) → H ＝ K
  all-elements-equal-is-iso-Large-Category =
    all-elements-equal-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)

  is-prop-is-iso-Large-Category :
    (f : hom-Large-Category C X Y) →
    is-prop (is-iso-Large-Category C f)
  is-prop-is-iso-Large-Category f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-iso-Large-Category f)

  is-iso-prop-Large-Category :
    (f : hom-Large-Category C X Y) → Prop (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-prop-Large-Category =
    is-iso-prop-Large-Precategory (large-precategory-Large-Category C)
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  where

  eq-iso-eq-hom-Large-Category :
    (f g : iso-Large-Category C X Y) →
    hom-iso-Large-Category C f ＝ hom-iso-Large-Category C g → f ＝ g
  eq-iso-eq-hom-Large-Category =
    eq-iso-eq-hom-Large-Precategory (large-precategory-Large-Category C)
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  where

  is-set-iso-Large-Category : is-set (iso-Large-Category C X Y)
  is-set-iso-Large-Category =
    is-set-iso-Large-Precategory (large-precategory-Large-Category C)

  iso-set-Large-Category : Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  iso-set-Large-Category =
    iso-set-Large-Precategory (large-precategory-Large-Category C) {X = X} {Y}
```

### Isomorphisms are closed under composition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 l3 : Level}
  {X : obj-Large-Category C l1}
  {Y : obj-Large-Category C l2}
  {Z : obj-Large-Category C l3}
  {g : hom-Large-Category C Y Z}
  {f : hom-Large-Category C X Y}
  where

  hom-comp-is-iso-Large-Category :
    is-iso-Large-Category C g →
    is-iso-Large-Category C f →
    hom-Large-Category C Z X
  hom-comp-is-iso-Large-Category =
    hom-comp-is-iso-Large-Precategory (large-precategory-Large-Category C)

  is-section-comp-is-iso-Large-Category :
    (q : is-iso-Large-Category C g)
    (p : is-iso-Large-Category C f) →
    comp-hom-Large-Category C
      ( comp-hom-Large-Category C g f)
      ( hom-comp-is-iso-Large-Category q p) ＝
    id-hom-Large-Category C
  is-section-comp-is-iso-Large-Category =
    is-section-comp-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)

  is-retraction-comp-is-iso-Large-Category :
    (q : is-iso-Large-Category C g)
    (p : is-iso-Large-Category C f) →
    comp-hom-Large-Category C
      ( hom-comp-is-iso-Large-Category q p)
      ( comp-hom-Large-Category C g f) ＝
    id-hom-Large-Category C
  is-retraction-comp-is-iso-Large-Category =
    is-retraction-comp-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)

  is-iso-comp-is-iso-Large-Category :
    is-iso-Large-Category C g → is-iso-Large-Category C f →
    is-iso-Large-Category C (comp-hom-Large-Category C g f)
  is-iso-comp-is-iso-Large-Category =
    is-iso-comp-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
```

### Composition of isomorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 l3 : Level}
  {X : obj-Large-Category C l1}
  {Y : obj-Large-Category C l2}
  {Z : obj-Large-Category C l3}
  (g : iso-Large-Category C Y Z)
  (f : iso-Large-Category C X Y)
  where

  hom-comp-iso-Large-Category :
    hom-Large-Category C X Z
  hom-comp-iso-Large-Category =
    hom-comp-iso-Large-Precategory (large-precategory-Large-Category C) g f

  is-iso-comp-iso-Large-Category :
    is-iso-Large-Category C hom-comp-iso-Large-Category
  is-iso-comp-iso-Large-Category =
    is-iso-comp-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( g)
      ( f)

  comp-iso-Large-Category :
    iso-Large-Category C X Z
  comp-iso-Large-Category =
    comp-iso-Large-Precategory (large-precategory-Large-Category C) g f

  hom-inv-comp-iso-Large-Category :
    hom-Large-Category C Z X
  hom-inv-comp-iso-Large-Category =
    hom-inv-iso-Large-Category C comp-iso-Large-Category

  is-section-inv-comp-iso-Large-Category :
    comp-hom-Large-Category C
      ( hom-comp-iso-Large-Category)
      ( hom-inv-comp-iso-Large-Category) ＝
    id-hom-Large-Category C
  is-section-inv-comp-iso-Large-Category =
    is-section-hom-inv-iso-Large-Category C comp-iso-Large-Category

  is-retraction-inv-comp-iso-Large-Category :
    comp-hom-Large-Category C
      ( hom-inv-comp-iso-Large-Category)
      ( hom-comp-iso-Large-Category) ＝
    id-hom-Large-Category C
  is-retraction-inv-comp-iso-Large-Category =
    is-retraction-hom-inv-iso-Large-Category C comp-iso-Large-Category
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  {f : hom-Large-Category C X Y}
  where

  is-iso-inv-is-iso-Large-Category :
    (p : is-iso-Large-Category C f) →
    is-iso-Large-Category C (hom-inv-iso-Large-Category C (f , p))
  pr1 (is-iso-inv-is-iso-Large-Category p) = f
  pr1 (pr2 (is-iso-inv-is-iso-Large-Category p)) =
    is-retraction-hom-inv-is-iso-Large-Category C f p
  pr2 (pr2 (is-iso-inv-is-iso-Large-Category p)) =
    is-section-hom-inv-is-iso-Large-Category C f p
```

### Inverses of isomorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  where

  inv-iso-Large-Category :
    iso-Large-Category C X Y →
    iso-Large-Category C Y X
  pr1 (inv-iso-Large-Category f) = hom-inv-iso-Large-Category C f
  pr2 (inv-iso-Large-Category f) =
    is-iso-inv-is-iso-Large-Category C
      ( is-iso-iso-Large-Category C f)
```

### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  (f : iso-Large-Category C X Y)
  where

  left-unit-law-comp-iso-Large-Category :
    comp-iso-Large-Category C (id-iso-Large-Category C) f ＝ f
  left-unit-law-comp-iso-Large-Category =
    left-unit-law-comp-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)

  right-unit-law-comp-iso-Large-Category :
    comp-iso-Large-Category C f (id-iso-Large-Category C) ＝ f
  right-unit-law-comp-iso-Large-Category =
    right-unit-law-comp-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)
```

### Composition of isomorphisms is associative

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 l3 l4 : Level}
  {X : obj-Large-Category C l1}
  {Y : obj-Large-Category C l2}
  {Z : obj-Large-Category C l3}
  {W : obj-Large-Category C l4}
  (h : iso-Large-Category C Z W)
  (g : iso-Large-Category C Y Z)
  (f : iso-Large-Category C X Y)
  where

  associative-comp-iso-Large-Category :
    comp-iso-Large-Category C (comp-iso-Large-Category C h g) f ＝
    comp-iso-Large-Category C h (comp-iso-Large-Category C g f)
  associative-comp-iso-Large-Category =
    associative-comp-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( h)
      ( g)
      ( f)
```

### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  (f : iso-Large-Category C X Y)
  where

  left-inverse-law-comp-iso-Large-Category :
    comp-iso-Large-Category C (inv-iso-Large-Category C f) f ＝
    id-iso-Large-Category C
  left-inverse-law-comp-iso-Large-Category =
    left-inverse-law-comp-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)

  right-inverse-law-comp-iso-Large-Category :
    comp-iso-Large-Category C f (inv-iso-Large-Category C f) ＝
    id-iso-Large-Category C
  right-inverse-law-comp-iso-Large-Category =
    right-inverse-law-comp-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( f)
```

### A morphism `f` is an isomorphism if and only if precomposition by `f` is an equivalence

**Proof:** If `f` is an isomorphism with inverse `f⁻¹`, then precomposing with
`f⁻¹` is an inverse of precomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that precomposing with `f` is an equivalence, for any object `Z`. Then

```text
  - ∘ f : hom Y X → hom X X
```

is an equivalence. In particular, there is a unique morphism `g : Y → X` such
that `g ∘ f ＝ id`. Thus we have a retraction of `f`. To see that `g` is also a
section, note that the map

```text
  - ∘ f : hom Y Y → hom X Y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `(f ∘ g) ∘ f ＝ id ∘ f`. To see this, we calculate

```text
  (f ∘ g) ∘ f ＝ f ∘ (g ∘ f) ＝ f ∘ id ＝ f ＝ id ∘ f.
```

This completes the proof.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  {f : hom-Large-Category C X Y}
  (H :
    {l3 : Level} (Z : obj-Large-Category C l3) →
    is-equiv (precomp-hom-Large-Category C f Z))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Large-Category :
    hom-Large-Category C Y X
  hom-inv-is-iso-is-equiv-precomp-hom-Large-Category =
    hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Category :
    comp-hom-Large-Category C
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Category)
      ( f) ＝
    id-hom-Large-Category C
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Category =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Category :
    comp-hom-Large-Category C
      ( f)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Category) ＝
    id-hom-Large-Category C
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Category =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

  is-iso-is-equiv-precomp-hom-Large-Category :
    is-iso-Large-Category C f
  is-iso-is-equiv-precomp-hom-Large-Category =
    is-iso-is-equiv-precomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 l3 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  {f : hom-Large-Category C X Y}
  (is-iso-f : is-iso-Large-Category C f)
  (Z : obj-Large-Category C l3)
  where

  map-inv-precomp-hom-is-iso-Large-Category :
    hom-Large-Category C X Z → hom-Large-Category C Y Z
  map-inv-precomp-hom-is-iso-Large-Category =
    precomp-hom-Large-Category C
      ( hom-inv-is-iso-Large-Category C f is-iso-f)
      ( Z)

  is-equiv-precomp-hom-is-iso-Large-Category :
    is-equiv (precomp-hom-Large-Category C f Z)
  is-equiv-precomp-hom-is-iso-Large-Category =
    is-equiv-precomp-hom-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( is-iso-f)
      ( Z)

  equiv-precomp-hom-is-iso-Large-Category :
    hom-Large-Category C Y Z ≃ hom-Large-Category C X Z
  equiv-precomp-hom-is-iso-Large-Category =
    equiv-precomp-hom-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( is-iso-f)
      ( Z)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 l3 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  (f : iso-Large-Category C X Y)
  (Z : obj-Large-Category C l3)
  where

  is-equiv-precomp-hom-iso-Large-Category :
    is-equiv (precomp-hom-Large-Category C (hom-iso-Large-Category C f) Z)
  is-equiv-precomp-hom-iso-Large-Category =
    is-equiv-precomp-hom-is-iso-Large-Category C
      ( is-iso-iso-Large-Category C f)
      ( Z)

  equiv-precomp-hom-iso-Large-Category :
    hom-Large-Category C Y Z ≃ hom-Large-Category C X Z
  equiv-precomp-hom-iso-Large-Category =
    equiv-precomp-hom-is-iso-Large-Category C
      ( is-iso-iso-Large-Category C f)
      ( Z)
```

### A morphism `f` is an isomorphism if and only if postcomposition by `f` is an equivalence

**Proof:** If `f` is an isomorphism with inverse `f⁻¹`, then postcomposing with
`f⁻¹` is an inverse of postcomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that postcomposing with `f` is an equivalence, for any object `Z`. Then

```text
  f ∘ - : hom Y X → hom Y Y
```

is an equivalence. In particular, there is a unique morphism `g : Y → X` such
that `f ∘ g ＝ id`. Thus we have a section of `f`. To see that `g` is also a
retraction, note that the map

```text
  f ∘ - : hom X X → hom X Y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `f ∘ (g ∘ f) ＝ f ∘ id`. To see this, we calculate

```text
  f ∘ (g ∘ f) ＝ (f ∘ g) ∘ f ＝ id ∘ f ＝ f ＝ f ∘ id.
```

This completes the proof.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  {f : hom-Large-Category C X Y}
  (H :
    {l3 : Level} (Z : obj-Large-Category C l3) →
    is-equiv (postcomp-hom-Large-Category C Z f))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category :
    hom-Large-Category C Y X
  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category =
    hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category :
    comp-hom-Large-Category C
      ( f)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category) ＝
    id-hom-Large-Category C
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category :
    comp-hom-Large-Category C
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category)
      ( f) ＝
    id-hom-Large-Category C
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Category =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

  is-iso-is-equiv-postcomp-hom-Large-Category :
    is-iso-Large-Category C f
  is-iso-is-equiv-postcomp-hom-Large-Category =
    is-iso-is-equiv-postcomp-hom-Large-Precategory
      ( large-precategory-Large-Category C)
      ( H)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 l3 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  {f : hom-Large-Category C X Y}
  (is-iso-f : is-iso-Large-Category C f)
  (Z : obj-Large-Category C l3)
  where

  map-inv-postcomp-hom-is-iso-Large-Category :
    hom-Large-Category C Z Y → hom-Large-Category C Z X
  map-inv-postcomp-hom-is-iso-Large-Category =
    postcomp-hom-Large-Category C
      ( Z)
      ( hom-inv-is-iso-Large-Category C f is-iso-f)

  is-equiv-postcomp-hom-is-iso-Large-Category :
    is-equiv (postcomp-hom-Large-Category C Z f)
  is-equiv-postcomp-hom-is-iso-Large-Category =
    is-equiv-postcomp-hom-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( is-iso-f)
      ( Z)

  equiv-postcomp-hom-is-iso-Large-Category :
    hom-Large-Category C Z X ≃ hom-Large-Category C Z Y
  equiv-postcomp-hom-is-iso-Large-Category =
    equiv-postcomp-hom-is-iso-Large-Precategory
      ( large-precategory-Large-Category C)
      ( is-iso-f)
      ( Z)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Category α β) {l1 l2 l3 : Level}
  {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
  (f : iso-Large-Category C X Y)
  (Z : obj-Large-Category C l3)
  where

  is-equiv-postcomp-hom-iso-Large-Category :
    is-equiv
      ( postcomp-hom-Large-Category C Z (hom-iso-Large-Category C f))
  is-equiv-postcomp-hom-iso-Large-Category =
    is-equiv-postcomp-hom-is-iso-Large-Category C
      ( is-iso-iso-Large-Category C f)
      ( Z)

  equiv-postcomp-hom-iso-Large-Category :
    hom-Large-Category C Z X ≃ hom-Large-Category C Z Y
  equiv-postcomp-hom-iso-Large-Category =
    equiv-postcomp-hom-is-iso-Large-Category C
      ( is-iso-iso-Large-Category C f)
      ( Z)
```
