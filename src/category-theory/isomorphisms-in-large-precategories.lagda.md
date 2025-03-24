# Isomorphisms in large precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.isomorphisms-in-large-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories funext univalence truncations
open import category-theory.large-precategories funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.injective-maps funext
open import foundation.propositions funext univalence
open import foundation.retractions funext
open import foundation.sections funext
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels
```

</details>

## Idea

An **isomorphism** in a
[large precategory](category-theory.large-precategories.md) `C` is a morphism
`f : X → Y` in `C` for which there exists a morphism `g : Y → X` such that
`f ∘ g ＝ id` and `g ∘ f ＝ id`.

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : hom-Large-Precategory C X Y)
  where

  is-iso-Large-Precategory : UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  is-iso-Large-Precategory =
    Σ ( hom-Large-Precategory C Y X)
      ( λ g →
        ( comp-hom-Large-Precategory C f g ＝ id-hom-Large-Precategory C) ×
        ( comp-hom-Large-Precategory C g f ＝ id-hom-Large-Precategory C))

  hom-inv-is-iso-Large-Precategory :
    is-iso-Large-Precategory → hom-Large-Precategory C Y X
  hom-inv-is-iso-Large-Precategory = pr1

  is-section-hom-inv-is-iso-Large-Precategory :
    (H : is-iso-Large-Precategory) →
    comp-hom-Large-Precategory C f (hom-inv-is-iso-Large-Precategory H) ＝
    id-hom-Large-Precategory C
  is-section-hom-inv-is-iso-Large-Precategory = pr1 ∘ pr2

  is-retraction-hom-inv-is-iso-Large-Precategory :
    (H : is-iso-Large-Precategory) →
    comp-hom-Large-Precategory C (hom-inv-is-iso-Large-Precategory H) f ＝
    id-hom-Large-Precategory C
  is-retraction-hom-inv-is-iso-Large-Precategory = pr2 ∘ pr2
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
    Σ (hom-Large-Precategory C X Y) (is-iso-Large-Precategory C)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : iso-Large-Precategory C X Y)
  where

  hom-iso-Large-Precategory : hom-Large-Precategory C X Y
  hom-iso-Large-Precategory = pr1 f

  is-iso-iso-Large-Precategory :
    is-iso-Large-Precategory C hom-iso-Large-Precategory
  is-iso-iso-Large-Precategory = pr2 f

  hom-inv-iso-Large-Precategory : hom-Large-Precategory C Y X
  hom-inv-iso-Large-Precategory = pr1 (pr2 f)

  is-section-hom-inv-iso-Large-Precategory :
    ( comp-hom-Large-Precategory C
      ( hom-iso-Large-Precategory)
      ( hom-inv-iso-Large-Precategory)) ＝
    ( id-hom-Large-Precategory C)
  is-section-hom-inv-iso-Large-Precategory = pr1 (pr2 (pr2 f))

  is-retraction-hom-inv-iso-Large-Precategory :
    ( comp-hom-Large-Precategory C
      ( hom-inv-iso-Large-Precategory)
      ( hom-iso-Large-Precategory)) ＝
    ( id-hom-Large-Precategory C)
  is-retraction-hom-inv-iso-Large-Precategory = pr2 (pr2 (pr2 f))
```

## Examples

### The identity isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = id_x` (it is its own inverse).

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 : Level} {X : obj-Large-Precategory C l1}
  where

  is-iso-id-hom-Large-Precategory :
    is-iso-Large-Precategory C (id-hom-Large-Precategory C {X = X})
  pr1 is-iso-id-hom-Large-Precategory = id-hom-Large-Precategory C
  pr1 (pr2 is-iso-id-hom-Large-Precategory) =
    left-unit-law-comp-hom-Large-Precategory C (id-hom-Large-Precategory C)
  pr2 (pr2 is-iso-id-hom-Large-Precategory) =
    left-unit-law-comp-hom-Large-Precategory C (id-hom-Large-Precategory C)

  id-iso-Large-Precategory : iso-Large-Precategory C X X
  pr1 id-iso-Large-Precategory = id-hom-Large-Precategory C
  pr2 id-iso-Large-Precategory = is-iso-id-hom-Large-Precategory
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
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  all-elements-equal-is-iso-Large-Precategory :
    (f : hom-Large-Precategory C X Y)
    (H K : is-iso-Large-Precategory C f) → H ＝ K
  all-elements-equal-is-iso-Large-Precategory f (g , p , q) (g' , p' , q') =
    eq-type-subtype
      ( λ g →
        product-Prop
          ( Id-Prop
            ( hom-set-Large-Precategory C Y Y)
            ( comp-hom-Large-Precategory C f g)
            ( id-hom-Large-Precategory C))
          ( Id-Prop
            ( hom-set-Large-Precategory C X X)
            ( comp-hom-Large-Precategory C g f)
            ( id-hom-Large-Precategory C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precategory C g)) ∙
        ( ap ( comp-hom-Large-Precategory C g) (inv p')) ∙
        ( inv (associative-comp-hom-Large-Precategory C g f g')) ∙
        ( ap ( comp-hom-Large-Precategory' C g') q) ∙
        ( left-unit-law-comp-hom-Large-Precategory C g'))

  is-prop-is-iso-Large-Precategory :
    (f : hom-Large-Precategory C X Y) →
    is-prop (is-iso-Large-Precategory C f)
  is-prop-is-iso-Large-Precategory f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-iso-Large-Precategory f)

  is-iso-prop-Large-Precategory :
    (f : hom-Large-Precategory C X Y) → Prop (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 (is-iso-prop-Large-Precategory f) =
    is-iso-Large-Precategory C f
  pr2 (is-iso-prop-Large-Precategory f) =
    is-prop-is-iso-Large-Precategory f
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  eq-iso-eq-hom-Large-Precategory :
    (f g : iso-Large-Precategory C X Y) →
    hom-iso-Large-Precategory C f ＝ hom-iso-Large-Precategory C g → f ＝ g
  eq-iso-eq-hom-Large-Precategory f g =
    eq-type-subtype (is-iso-prop-Large-Precategory C)
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  is-set-iso-Large-Precategory : is-set (iso-Large-Precategory C X Y)
  is-set-iso-Large-Precategory =
    is-set-type-subtype
      ( is-iso-prop-Large-Precategory C)
      ( is-set-hom-Large-Precategory C X Y)

  iso-set-Large-Precategory : Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-set-Large-Precategory = iso-Large-Precategory C X Y
  pr2 iso-set-Large-Precategory = is-set-iso-Large-Precategory
```

### Equalities induce isomorphisms

An equality between objects `X Y : A` gives rise to an isomorphism between them.
This is because, by the J-rule, it is enough to construct an isomorphism given
`refl : X ＝ X`, from `X` to itself. We take the identity morphism as such an
isomorphism.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 : Level}
  where

  iso-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) → X ＝ Y → iso-Large-Precategory C X Y
  pr1 (iso-eq-Large-Precategory X Y p) = hom-eq-Large-Precategory C X Y p
  pr2 (iso-eq-Large-Precategory X .X refl) = is-iso-id-hom-Large-Precategory C

  compute-iso-eq-Large-Precategory :
    (X Y : obj-Large-Precategory C l1) →
    iso-eq-Precategory (precategory-Large-Precategory C l1) X Y ~
    iso-eq-Large-Precategory X Y
  compute-iso-eq-Large-Precategory X Y p =
    eq-iso-eq-hom-Large-Precategory C
      ( iso-eq-Precategory (precategory-Large-Precategory C l1) X Y p)
      ( iso-eq-Large-Precategory X Y p)
      ( compute-hom-eq-Large-Precategory C X Y p)
```

### Isomorphisms are closed under composition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precategory C l1}
  {Y : obj-Large-Precategory C l2}
  {Z : obj-Large-Precategory C l3}
  {g : hom-Large-Precategory C Y Z}
  {f : hom-Large-Precategory C X Y}
  where

  hom-comp-is-iso-Large-Precategory :
    is-iso-Large-Precategory C g →
    is-iso-Large-Precategory C f →
    hom-Large-Precategory C Z X
  hom-comp-is-iso-Large-Precategory q p =
    comp-hom-Large-Precategory C
      ( hom-inv-is-iso-Large-Precategory C f p)
      ( hom-inv-is-iso-Large-Precategory C g q)

  is-section-comp-is-iso-Large-Precategory :
    (q : is-iso-Large-Precategory C g)
    (p : is-iso-Large-Precategory C f) →
    comp-hom-Large-Precategory C
      ( comp-hom-Large-Precategory C g f)
      ( hom-comp-is-iso-Large-Precategory q p) ＝
    id-hom-Large-Precategory C
  is-section-comp-is-iso-Large-Precategory q p =
    ( associative-comp-hom-Large-Precategory C g f _) ∙
    ( ap
      ( comp-hom-Large-Precategory C g)
      ( ( inv
          ( associative-comp-hom-Large-Precategory C f
            ( hom-inv-is-iso-Large-Precategory C f p)
            ( hom-inv-is-iso-Large-Precategory C g q))) ∙
        ( ap
          ( λ h → comp-hom-Large-Precategory C h _)
          ( is-section-hom-inv-is-iso-Large-Precategory C f p)) ∙
        ( left-unit-law-comp-hom-Large-Precategory C
          ( hom-inv-is-iso-Large-Precategory C g q)))) ∙
    ( is-section-hom-inv-is-iso-Large-Precategory C g q)

  is-retraction-comp-is-iso-Large-Precategory :
    (q : is-iso-Large-Precategory C g)
    (p : is-iso-Large-Precategory C f) →
    comp-hom-Large-Precategory C
      ( hom-comp-is-iso-Large-Precategory q p)
      ( comp-hom-Large-Precategory C g f) ＝
    id-hom-Large-Precategory C
  is-retraction-comp-is-iso-Large-Precategory q p =
    ( associative-comp-hom-Large-Precategory C
      ( hom-inv-is-iso-Large-Precategory C f p)
      ( hom-inv-is-iso-Large-Precategory C g q)
      ( comp-hom-Large-Precategory C g f)) ∙
    ( ap
      ( comp-hom-Large-Precategory
        ( C)
        ( hom-inv-is-iso-Large-Precategory C f p))
      ( ( inv
          ( associative-comp-hom-Large-Precategory C
            ( hom-inv-is-iso-Large-Precategory C g q)
            ( g)
            ( f))) ∙
        ( ap
          ( λ h → comp-hom-Large-Precategory C h f)
          ( is-retraction-hom-inv-is-iso-Large-Precategory C g q)) ∙
        ( left-unit-law-comp-hom-Large-Precategory C f))) ∙
    ( is-retraction-hom-inv-is-iso-Large-Precategory C f p)

  is-iso-comp-is-iso-Large-Precategory :
    is-iso-Large-Precategory C g → is-iso-Large-Precategory C f →
    is-iso-Large-Precategory C (comp-hom-Large-Precategory C g f)
  pr1 (is-iso-comp-is-iso-Large-Precategory q p) =
    hom-comp-is-iso-Large-Precategory q p
  pr1 (pr2 (is-iso-comp-is-iso-Large-Precategory q p)) =
    is-section-comp-is-iso-Large-Precategory q p
  pr2 (pr2 (is-iso-comp-is-iso-Large-Precategory q p)) =
    is-retraction-comp-is-iso-Large-Precategory q p
```

### Composition of isomorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precategory C l1}
  {Y : obj-Large-Precategory C l2}
  {Z : obj-Large-Precategory C l3}
  (g : iso-Large-Precategory C Y Z)
  (f : iso-Large-Precategory C X Y)
  where

  hom-comp-iso-Large-Precategory :
    hom-Large-Precategory C X Z
  hom-comp-iso-Large-Precategory =
    comp-hom-Large-Precategory C
      ( hom-iso-Large-Precategory C g)
      ( hom-iso-Large-Precategory C f)

  is-iso-comp-iso-Large-Precategory :
    is-iso-Large-Precategory C hom-comp-iso-Large-Precategory
  is-iso-comp-iso-Large-Precategory =
    is-iso-comp-is-iso-Large-Precategory C
      ( is-iso-iso-Large-Precategory C g)
      ( is-iso-iso-Large-Precategory C f)

  comp-iso-Large-Precategory :
    iso-Large-Precategory C X Z
  pr1 comp-iso-Large-Precategory = hom-comp-iso-Large-Precategory
  pr2 comp-iso-Large-Precategory = is-iso-comp-iso-Large-Precategory

  hom-inv-comp-iso-Large-Precategory :
    hom-Large-Precategory C Z X
  hom-inv-comp-iso-Large-Precategory =
    hom-inv-iso-Large-Precategory C comp-iso-Large-Precategory

  is-section-inv-comp-iso-Large-Precategory :
    comp-hom-Large-Precategory C
      ( hom-comp-iso-Large-Precategory)
      ( hom-inv-comp-iso-Large-Precategory) ＝
    id-hom-Large-Precategory C
  is-section-inv-comp-iso-Large-Precategory =
    is-section-hom-inv-iso-Large-Precategory C comp-iso-Large-Precategory

  is-retraction-inv-comp-iso-Large-Precategory :
    comp-hom-Large-Precategory C
      ( hom-inv-comp-iso-Large-Precategory)
      ( hom-comp-iso-Large-Precategory) ＝
    id-hom-Large-Precategory C
  is-retraction-inv-comp-iso-Large-Precategory =
    is-retraction-hom-inv-iso-Large-Precategory C comp-iso-Large-Precategory
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  {f : hom-Large-Precategory C X Y}
  where

  is-iso-inv-is-iso-Large-Precategory :
    (p : is-iso-Large-Precategory C f) →
    is-iso-Large-Precategory C (hom-inv-iso-Large-Precategory C (f , p))
  pr1 (is-iso-inv-is-iso-Large-Precategory p) = f
  pr1 (pr2 (is-iso-inv-is-iso-Large-Precategory p)) =
    is-retraction-hom-inv-is-iso-Large-Precategory C f p
  pr2 (pr2 (is-iso-inv-is-iso-Large-Precategory p)) =
    is-section-hom-inv-is-iso-Large-Precategory C f p
```

### Inverses of isomorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  where

  inv-iso-Large-Precategory :
    iso-Large-Precategory C X Y → iso-Large-Precategory C Y X
  pr1 (inv-iso-Large-Precategory f) = hom-inv-iso-Large-Precategory C f
  pr2 (inv-iso-Large-Precategory f) =
    is-iso-inv-is-iso-Large-Precategory C
      ( is-iso-iso-Large-Precategory C f)
```

### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : iso-Large-Precategory C X Y)
  where

  left-unit-law-comp-iso-Large-Precategory :
    comp-iso-Large-Precategory C (id-iso-Large-Precategory C) f ＝ f
  left-unit-law-comp-iso-Large-Precategory =
    eq-iso-eq-hom-Large-Precategory C
      ( comp-iso-Large-Precategory C (id-iso-Large-Precategory C) f)
      ( f)
      ( left-unit-law-comp-hom-Large-Precategory C
        ( hom-iso-Large-Precategory C f))

  right-unit-law-comp-iso-Large-Precategory :
    comp-iso-Large-Precategory C f (id-iso-Large-Precategory C) ＝ f
  right-unit-law-comp-iso-Large-Precategory =
    eq-iso-eq-hom-Large-Precategory C
      ( comp-iso-Large-Precategory C f (id-iso-Large-Precategory C))
      ( f)
      ( right-unit-law-comp-hom-Large-Precategory C
        ( hom-iso-Large-Precategory C f))
```

### Composition of isomorphisms is associative

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 l4 : Level}
  {X : obj-Large-Precategory C l1}
  {Y : obj-Large-Precategory C l2}
  {Z : obj-Large-Precategory C l3}
  {W : obj-Large-Precategory C l4}
  (h : iso-Large-Precategory C Z W)
  (g : iso-Large-Precategory C Y Z)
  (f : iso-Large-Precategory C X Y)
  where

  associative-comp-iso-Large-Precategory :
    comp-iso-Large-Precategory C (comp-iso-Large-Precategory C h g) f ＝
    comp-iso-Large-Precategory C h (comp-iso-Large-Precategory C g f)
  associative-comp-iso-Large-Precategory =
    eq-iso-eq-hom-Large-Precategory C
      ( comp-iso-Large-Precategory C (comp-iso-Large-Precategory C h g) f)
      ( comp-iso-Large-Precategory C h (comp-iso-Large-Precategory C g f))
      ( associative-comp-hom-Large-Precategory C
        ( hom-iso-Large-Precategory C h)
        ( hom-iso-Large-Precategory C g)
        ( hom-iso-Large-Precategory C f))
```

### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : iso-Large-Precategory C X Y)
  where

  left-inverse-law-comp-iso-Large-Precategory :
    comp-iso-Large-Precategory C (inv-iso-Large-Precategory C f) f ＝
    id-iso-Large-Precategory C
  left-inverse-law-comp-iso-Large-Precategory =
    eq-iso-eq-hom-Large-Precategory C
      ( comp-iso-Large-Precategory C (inv-iso-Large-Precategory C f) f)
      ( id-iso-Large-Precategory C)
      ( is-retraction-hom-inv-iso-Large-Precategory C f)

  right-inverse-law-comp-iso-Large-Precategory :
    comp-iso-Large-Precategory C f (inv-iso-Large-Precategory C f) ＝
    id-iso-Large-Precategory C
  right-inverse-law-comp-iso-Large-Precategory =
    eq-iso-eq-hom-Large-Precategory C
      ( comp-iso-Large-Precategory C f (inv-iso-Large-Precategory C f))
      ( id-iso-Large-Precategory C)
      ( is-section-hom-inv-iso-Large-Precategory C f)
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
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  {f : hom-Large-Precategory C X Y}
  (H :
    {l3 : Level} (Z : obj-Large-Precategory C l3) →
    is-equiv (precomp-hom-Large-Precategory C f Z))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory :
    hom-Large-Precategory C Y X
  hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory =
    map-inv-is-equiv (H X) (id-hom-Large-Precategory C)

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory :
    comp-hom-Large-Precategory C
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory)
      ( f) ＝
    id-hom-Large-Precategory C
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory =
    is-section-map-inv-is-equiv (H X) (id-hom-Large-Precategory C)

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory :
    comp-hom-Large-Precategory C
      ( f)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory) ＝
    id-hom-Large-Precategory C
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory =
    is-injective-is-equiv
      ( H Y)
      ( ( associative-comp-hom-Large-Precategory C
          ( f)
          ( hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory)
          ( f)) ∙
        ( ap
          ( comp-hom-Large-Precategory C f)
          ( is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory)) ∙
        ( right-unit-law-comp-hom-Large-Precategory C f) ∙
        ( inv (left-unit-law-comp-hom-Large-Precategory C f)))

  is-iso-is-equiv-precomp-hom-Large-Precategory :
    is-iso-Large-Precategory C f
  pr1 is-iso-is-equiv-precomp-hom-Large-Precategory =
    hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory
  pr1 (pr2 is-iso-is-equiv-precomp-hom-Large-Precategory) =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory
  pr2 (pr2 is-iso-is-equiv-precomp-hom-Large-Precategory) =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Large-Precategory

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  {f : hom-Large-Precategory C X Y}
  (is-iso-f : is-iso-Large-Precategory C f)
  (Z : obj-Large-Precategory C l3)
  where

  map-inv-precomp-hom-is-iso-Large-Precategory :
    hom-Large-Precategory C X Z → hom-Large-Precategory C Y Z
  map-inv-precomp-hom-is-iso-Large-Precategory =
    precomp-hom-Large-Precategory C
      ( hom-inv-is-iso-Large-Precategory C f is-iso-f)
      ( Z)

  is-section-map-inv-precomp-hom-is-iso-Large-Precategory :
    is-section
      ( precomp-hom-Large-Precategory C f Z)
      ( map-inv-precomp-hom-is-iso-Large-Precategory)
  is-section-map-inv-precomp-hom-is-iso-Large-Precategory g =
    ( associative-comp-hom-Large-Precategory C
      ( g)
      ( hom-inv-is-iso-Large-Precategory C f is-iso-f)
      ( f)) ∙
    ( ap
      ( comp-hom-Large-Precategory C g)
      ( is-retraction-hom-inv-is-iso-Large-Precategory C f is-iso-f)) ∙
    ( right-unit-law-comp-hom-Large-Precategory C g)

  is-retraction-map-inv-precomp-hom-is-iso-Large-Precategory :
    is-retraction
      ( precomp-hom-Large-Precategory C f Z)
      ( map-inv-precomp-hom-is-iso-Large-Precategory)
  is-retraction-map-inv-precomp-hom-is-iso-Large-Precategory g =
    ( associative-comp-hom-Large-Precategory C
      ( g)
      ( f)
      ( hom-inv-is-iso-Large-Precategory C f is-iso-f)) ∙
    ( ap
      ( comp-hom-Large-Precategory C g)
      ( is-section-hom-inv-is-iso-Large-Precategory C f is-iso-f)) ∙
    ( right-unit-law-comp-hom-Large-Precategory C g)

  is-equiv-precomp-hom-is-iso-Large-Precategory :
    is-equiv (precomp-hom-Large-Precategory C f Z)
  is-equiv-precomp-hom-is-iso-Large-Precategory =
    is-equiv-is-invertible
      ( map-inv-precomp-hom-is-iso-Large-Precategory)
      ( is-section-map-inv-precomp-hom-is-iso-Large-Precategory)
      ( is-retraction-map-inv-precomp-hom-is-iso-Large-Precategory)

  equiv-precomp-hom-is-iso-Large-Precategory :
    hom-Large-Precategory C Y Z ≃ hom-Large-Precategory C X Z
  pr1 equiv-precomp-hom-is-iso-Large-Precategory =
    precomp-hom-Large-Precategory C f Z
  pr2 equiv-precomp-hom-is-iso-Large-Precategory =
    is-equiv-precomp-hom-is-iso-Large-Precategory

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : iso-Large-Precategory C X Y)
  (Z : obj-Large-Precategory C l3)
  where

  is-equiv-precomp-hom-iso-Large-Precategory :
    is-equiv (precomp-hom-Large-Precategory C (hom-iso-Large-Precategory C f) Z)
  is-equiv-precomp-hom-iso-Large-Precategory =
    is-equiv-precomp-hom-is-iso-Large-Precategory C
      ( is-iso-iso-Large-Precategory C f)
      ( Z)

  equiv-precomp-hom-iso-Large-Precategory :
    hom-Large-Precategory C Y Z ≃ hom-Large-Precategory C X Z
  equiv-precomp-hom-iso-Large-Precategory =
    equiv-precomp-hom-is-iso-Large-Precategory C
      ( is-iso-iso-Large-Precategory C f)
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
  (C : Large-Precategory α β) {l1 l2 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  {f : hom-Large-Precategory C X Y}
  (H :
    {l3 : Level} (Z : obj-Large-Precategory C l3) →
    is-equiv (postcomp-hom-Large-Precategory C Z f))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory :
    hom-Large-Precategory C Y X
  hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory =
    map-inv-is-equiv (H Y) (id-hom-Large-Precategory C)

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory :
    comp-hom-Large-Precategory C
      ( f)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory) ＝
    id-hom-Large-Precategory C
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory =
    is-section-map-inv-is-equiv (H Y) (id-hom-Large-Precategory C)

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory :
    comp-hom-Large-Precategory C
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory)
      ( f) ＝
    id-hom-Large-Precategory C
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory =
    is-injective-is-equiv
      ( H X)
      ( ( inv
          ( associative-comp-hom-Large-Precategory C
            ( f)
            ( hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory)
            ( f))) ∙
        ( ap
          ( comp-hom-Large-Precategory' C f)
          ( is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory)) ∙
        ( left-unit-law-comp-hom-Large-Precategory C f) ∙
        ( inv (right-unit-law-comp-hom-Large-Precategory C f)))

  is-iso-is-equiv-postcomp-hom-Large-Precategory :
    is-iso-Large-Precategory C f
  pr1 is-iso-is-equiv-postcomp-hom-Large-Precategory =
    hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory
  pr1 (pr2 is-iso-is-equiv-postcomp-hom-Large-Precategory) =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory
  pr2 (pr2 is-iso-is-equiv-postcomp-hom-Large-Precategory) =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Large-Precategory

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  {f : hom-Large-Precategory C X Y}
  (is-iso-f : is-iso-Large-Precategory C f)
  (Z : obj-Large-Precategory C l3)
  where

  map-inv-postcomp-hom-is-iso-Large-Precategory :
    hom-Large-Precategory C Z Y → hom-Large-Precategory C Z X
  map-inv-postcomp-hom-is-iso-Large-Precategory =
    postcomp-hom-Large-Precategory C
      ( Z)
      ( hom-inv-is-iso-Large-Precategory C f is-iso-f)

  is-section-map-inv-postcomp-hom-is-iso-Large-Precategory :
    is-section
      ( postcomp-hom-Large-Precategory C Z f)
      ( map-inv-postcomp-hom-is-iso-Large-Precategory)
  is-section-map-inv-postcomp-hom-is-iso-Large-Precategory g =
    ( inv
      ( associative-comp-hom-Large-Precategory C
        ( f)
        ( hom-inv-is-iso-Large-Precategory C f is-iso-f)
        ( g))) ∙
    ( ap
      ( comp-hom-Large-Precategory' C g)
      ( is-section-hom-inv-is-iso-Large-Precategory C f is-iso-f)) ∙
    ( left-unit-law-comp-hom-Large-Precategory C g)

  is-retraction-map-inv-postcomp-hom-is-iso-Large-Precategory :
    is-retraction
      ( postcomp-hom-Large-Precategory C Z f)
      ( map-inv-postcomp-hom-is-iso-Large-Precategory)
  is-retraction-map-inv-postcomp-hom-is-iso-Large-Precategory g =
    ( inv
      ( associative-comp-hom-Large-Precategory C
        ( hom-inv-is-iso-Large-Precategory C f is-iso-f)
        ( f)
        ( g))) ∙
    ( ap
      ( comp-hom-Large-Precategory' C g)
      ( is-retraction-hom-inv-is-iso-Large-Precategory C f is-iso-f)) ∙
    ( left-unit-law-comp-hom-Large-Precategory C g)

  is-equiv-postcomp-hom-is-iso-Large-Precategory :
    is-equiv (postcomp-hom-Large-Precategory C Z f)
  is-equiv-postcomp-hom-is-iso-Large-Precategory =
    is-equiv-is-invertible
      ( map-inv-postcomp-hom-is-iso-Large-Precategory)
      ( is-section-map-inv-postcomp-hom-is-iso-Large-Precategory)
      ( is-retraction-map-inv-postcomp-hom-is-iso-Large-Precategory)

  equiv-postcomp-hom-is-iso-Large-Precategory :
    hom-Large-Precategory C Z X ≃ hom-Large-Precategory C Z Y
  pr1 equiv-postcomp-hom-is-iso-Large-Precategory =
    postcomp-hom-Large-Precategory C Z f
  pr2 equiv-postcomp-hom-is-iso-Large-Precategory =
    is-equiv-postcomp-hom-is-iso-Large-Precategory

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precategory C l1} {Y : obj-Large-Precategory C l2}
  (f : iso-Large-Precategory C X Y)
  (Z : obj-Large-Precategory C l3)
  where

  is-equiv-postcomp-hom-iso-Large-Precategory :
    is-equiv
      ( postcomp-hom-Large-Precategory C Z (hom-iso-Large-Precategory C f))
  is-equiv-postcomp-hom-iso-Large-Precategory =
    is-equiv-postcomp-hom-is-iso-Large-Precategory C
      ( is-iso-iso-Large-Precategory C f)
      ( Z)

  equiv-postcomp-hom-iso-Large-Precategory :
    hom-Large-Precategory C Z X ≃ hom-Large-Precategory C Z Y
  equiv-postcomp-hom-iso-Large-Precategory =
    equiv-postcomp-hom-is-iso-Large-Precategory C
      ( is-iso-iso-Large-Precategory C f)
      ( Z)
```
