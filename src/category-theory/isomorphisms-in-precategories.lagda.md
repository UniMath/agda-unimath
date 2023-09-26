# Isomorphisms in precategories

```agda
module category-theory.isomorphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An **isomorphism** in a [precategory](category-theory.precategories.md) `C` is a
morphism `f : x → y` in `C` for which there exists a morphism `g : y → x` such
that `f ∘ g ＝ id` and `g ∘ f ＝ id`.

## Definitions

### The predicate of being an isomorphism in a precategory

```agda
is-iso-Precategory :
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : hom-Precategory C x y) →
  UU l2
is-iso-Precategory C {x} {y} f =
  Σ ( hom-Precategory C y x)
    ( λ g →
      ( comp-hom-Precategory C f g ＝ id-hom-Precategory C) ×
      ( comp-hom-Precategory C g f ＝ id-hom-Precategory C))

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  where

  hom-inv-is-iso-Precategory :
    is-iso-Precategory C f → hom-Precategory C y x
  hom-inv-is-iso-Precategory = pr1

  is-section-hom-inv-is-iso-Precategory :
    (H : is-iso-Precategory C f) →
    comp-hom-Precategory C f (hom-inv-is-iso-Precategory H) ＝
    id-hom-Precategory C
  is-section-hom-inv-is-iso-Precategory = pr1 ∘ pr2

  is-retraction-hom-inv-is-iso-Precategory :
    (H : is-iso-Precategory C f) →
    comp-hom-Precategory C (hom-inv-is-iso-Precategory H) f ＝
    id-hom-Precategory C
  is-retraction-hom-inv-is-iso-Precategory = pr2 ∘ pr2
```

### Isomorphisms in a precategory

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  (x y : obj-Precategory C)
  where

  iso-Precategory : UU l2
  iso-Precategory = Σ (hom-Precategory C x y) (is-iso-Precategory C)

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  hom-iso-Precategory : hom-Precategory C x y
  hom-iso-Precategory = pr1 f

  is-iso-iso-Precategory :
    is-iso-Precategory C hom-iso-Precategory
  is-iso-iso-Precategory = pr2 f

  hom-inv-iso-Precategory : hom-Precategory C y x
  hom-inv-iso-Precategory =
    hom-inv-is-iso-Precategory C
      ( is-iso-iso-Precategory)

  is-section-hom-inv-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-iso-Precategory)
      ( hom-inv-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-hom-inv-iso-Precategory =
    is-section-hom-inv-is-iso-Precategory C
      ( is-iso-iso-Precategory)

  is-retraction-hom-inv-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-iso-Precategory)
      ( hom-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-retraction-hom-inv-iso-Precategory =
    is-retraction-hom-inv-is-iso-Precategory C
      ( is-iso-iso-Precategory)
```

## Examples

### The identity isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = id_x` (it is its own inverse).

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x : obj-Precategory C}
  where

  is-iso-id-hom-Precategory :
    is-iso-Precategory C (id-hom-Precategory C {x})
  pr1 is-iso-id-hom-Precategory = id-hom-Precategory C
  pr1 (pr2 is-iso-id-hom-Precategory) =
    left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)
  pr2 (pr2 is-iso-id-hom-Precategory) =
    left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)

  id-iso-Precategory : iso-Precategory C x x
  pr1 id-iso-Precategory = id-hom-Precategory C
  pr2 id-iso-Precategory = is-iso-id-hom-Precategory
```

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because, by the J-rule, it is enough to construct an isomorphism given
`refl : x ＝ x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  iso-eq-Precategory :
    (x y : obj-Precategory C) →
    x ＝ y → iso-Precategory C x y
  iso-eq-Precategory x .x refl = id-iso-Precategory C

  compute-hom-iso-eq-Precategory :
    {x y : obj-Precategory C} →
    (p : x ＝ y) →
    hom-eq-Precategory C x y p ＝
    hom-iso-Precategory C (iso-eq-Precategory x y p)
  compute-hom-iso-eq-Precategory refl = refl
```

## Properties

### Being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to
`f`. It is enough to show that `g = g'` since the equalities are
[propositions](foundation-core.propositions.md) (since the hom-types are sets).
But we have the following chain of equalities:
`g = g ∘ id_y = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = id_x ∘ g' = g'`.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  all-elements-equal-is-iso-Precategory :
    (f : hom-Precategory C x y)
    (H K : is-iso-Precategory C f) → H ＝ K
  all-elements-equal-is-iso-Precategory f
    (g , p , q) (g' , p' , q') =
    eq-type-subtype
      ( λ g →
        prod-Prop
          ( Id-Prop
            ( hom-set-Precategory C y y)
            ( comp-hom-Precategory C f g)
            ( id-hom-Precategory C))
          ( Id-Prop
            ( hom-set-Precategory C x x)
            ( comp-hom-Precategory C g f)
            ( id-hom-Precategory C)))
      ( ( inv (right-unit-law-comp-hom-Precategory C g)) ∙
        ( ap ( comp-hom-Precategory C g) (inv p')) ∙
        ( inv (associative-comp-hom-Precategory C g f g')) ∙
        ( ap ( comp-hom-Precategory' C g') q) ∙
        ( left-unit-law-comp-hom-Precategory C g'))

  is-prop-is-iso-Precategory :
    (f : hom-Precategory C x y) →
    is-prop (is-iso-Precategory C f)
  is-prop-is-iso-Precategory f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-iso-Precategory f)

  is-iso-prop-Precategory :
    (f : hom-Precategory C x y) → Prop l2
  pr1 (is-iso-prop-Precategory f) = is-iso-Precategory C f
  pr2 (is-iso-prop-Precategory f) = is-prop-is-iso-Precategory f
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  eq-iso-eq-hom-Precategory :
    (f g : iso-Precategory C x y) →
    hom-iso-Precategory C f ＝ hom-iso-Precategory C g → f ＝ g
  eq-iso-eq-hom-Precategory f g =
    eq-type-subtype (is-iso-prop-Precategory C)
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a
[subtype](foundation-core.subtypes.md) of the [foundation-core.sets.md)
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-set-iso-Precategory : is-set (iso-Precategory C x y)
  is-set-iso-Precategory =
    is-set-type-subtype
      ( is-iso-prop-Precategory C)
      ( is-set-hom-Precategory C x y)

  iso-set-Precategory : Set l2
  pr1 iso-set-Precategory = iso-Precategory C x y
  pr2 iso-set-Precategory = is-set-iso-Precategory
```

### Isomorphisms are closed under composition

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  {g : hom-Precategory C y z}
  {f : hom-Precategory C x y}
  where

  hom-comp-is-iso-Precategory :
    is-iso-Precategory C g →
    is-iso-Precategory C f →
    hom-Precategory C z x
  hom-comp-is-iso-Precategory q p =
    comp-hom-Precategory C
      ( hom-inv-is-iso-Precategory C p)
      ( hom-inv-is-iso-Precategory C q)

  is-section-comp-is-iso-Precategory :
    (q : is-iso-Precategory C g)
    (p : is-iso-Precategory C f) →
    comp-hom-Precategory C
      ( comp-hom-Precategory C g f)
      ( hom-comp-is-iso-Precategory q p) ＝
    id-hom-Precategory C
  is-section-comp-is-iso-Precategory q p =
    ( associative-comp-hom-Precategory C g f _) ∙
    ( ap
      ( comp-hom-Precategory C g)
      ( ( inv
          ( associative-comp-hom-Precategory C f
            ( hom-inv-is-iso-Precategory C p)
            ( hom-inv-is-iso-Precategory C q))) ∙
        ( ap
          ( λ h →
            comp-hom-Precategory C h (hom-inv-is-iso-Precategory C q))
          ( is-section-hom-inv-is-iso-Precategory C p) ∙
          ( left-unit-law-comp-hom-Precategory C
            ( hom-inv-is-iso-Precategory C q))))) ∙
    ( is-section-hom-inv-is-iso-Precategory C q)

  is-retraction-comp-is-iso-Precategory :
    (q : is-iso-Precategory C g)
    (p : is-iso-Precategory C f) →
    ( comp-hom-Precategory C
      ( hom-comp-is-iso-Precategory q p)
      ( comp-hom-Precategory C g f)) ＝
    ( id-hom-Precategory C)
  is-retraction-comp-is-iso-Precategory q p =
    ( associative-comp-hom-Precategory C
      ( hom-inv-is-iso-Precategory C p)
      ( hom-inv-is-iso-Precategory C q)
      ( comp-hom-Precategory C g f)) ∙
    ( ap
      ( comp-hom-Precategory
        ( C)
        ( hom-inv-is-iso-Precategory C p))
      ( ( inv
          ( associative-comp-hom-Precategory C
            ( hom-inv-is-iso-Precategory C q)
            ( g)
            ( f))) ∙
        ( ap
            ( λ h → comp-hom-Precategory C h f)
            ( is-retraction-hom-inv-is-iso-Precategory C q)) ∙
        ( left-unit-law-comp-hom-Precategory C f))) ∙
    ( is-retraction-hom-inv-is-iso-Precategory C p)

  is-iso-comp-is-iso-Precategory :
    is-iso-Precategory C g → is-iso-Precategory C f →
    is-iso-Precategory C (comp-hom-Precategory C g f)
  pr1 (is-iso-comp-is-iso-Precategory q p) =
    hom-comp-is-iso-Precategory q p
  pr1 (pr2 (is-iso-comp-is-iso-Precategory q p)) =
    is-section-comp-is-iso-Precategory q p
  pr2 (pr2 (is-iso-comp-is-iso-Precategory q p)) =
    is-retraction-comp-is-iso-Precategory q p
```

### The composition operation on isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  (g : iso-Precategory C y z)
  (f : iso-Precategory C x y)
  where

  hom-comp-iso-Precategory :
    hom-Precategory C x z
  hom-comp-iso-Precategory =
    comp-hom-Precategory C
      ( hom-iso-Precategory C g)
      ( hom-iso-Precategory C f)

  is-iso-comp-iso-Precategory :
    is-iso-Precategory C hom-comp-iso-Precategory
  is-iso-comp-iso-Precategory =
    is-iso-comp-is-iso-Precategory C
      ( is-iso-iso-Precategory C g)
      ( is-iso-iso-Precategory C f)

  comp-iso-Precategory : iso-Precategory C x z
  pr1 comp-iso-Precategory = hom-comp-iso-Precategory
  pr2 comp-iso-Precategory = is-iso-comp-iso-Precategory

  hom-inv-comp-iso-Precategory : hom-Precategory C z x
  hom-inv-comp-iso-Precategory =
    hom-inv-iso-Precategory C comp-iso-Precategory

  is-section-inv-comp-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-comp-iso-Precategory)
      ( hom-inv-comp-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-inv-comp-iso-Precategory =
    is-section-hom-inv-iso-Precategory C comp-iso-Precategory

  is-retraction-inv-comp-iso-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-comp-iso-Precategory)
      ( hom-comp-iso-Precategory)) ＝
    ( id-hom-Precategory C)
  is-retraction-inv-comp-iso-Precategory =
    is-retraction-hom-inv-iso-Precategory C comp-iso-Precategory
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  where

  is-iso-inv-is-iso-Precategory :
    (p : is-iso-Precategory C f) →
    is-iso-Precategory C (hom-inv-iso-Precategory C (f , p))
  pr1 (is-iso-inv-is-iso-Precategory p) = f
  pr1 (pr2 (is-iso-inv-is-iso-Precategory p)) =
    is-retraction-hom-inv-is-iso-Precategory C p
  pr2 (pr2 (is-iso-inv-is-iso-Precategory p)) =
    is-section-hom-inv-is-iso-Precategory C p
```

### Inverses of isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  inv-iso-Precategory :
    iso-Precategory C x y → iso-Precategory C y x
  pr1 (inv-iso-Precategory f) = hom-inv-iso-Precategory C f
  pr2 (inv-iso-Precategory f) =
    is-iso-inv-is-iso-Precategory C (is-iso-iso-Precategory C f)
```

### Groupoid laws of isomorphisms in precategories

#### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  left-unit-law-comp-iso-Precategory :
    comp-iso-Precategory C (id-iso-Precategory C) f ＝ f
  left-unit-law-comp-iso-Precategory =
    eq-iso-eq-hom-Precategory C
      ( comp-iso-Precategory C (id-iso-Precategory C) f)
      ( f)
      ( left-unit-law-comp-hom-Precategory C
        ( hom-iso-Precategory C f))

  right-unit-law-comp-iso-Precategory :
    comp-iso-Precategory C f (id-iso-Precategory C) ＝ f
  right-unit-law-comp-iso-Precategory =
    eq-iso-eq-hom-Precategory C
      ( comp-iso-Precategory C f (id-iso-Precategory C))
      ( f)
      ( right-unit-law-comp-hom-Precategory C
        ( hom-iso-Precategory C f))
```

#### Composition of isomorphisms is associative

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z w : obj-Precategory C}
  (h : iso-Precategory C z w)
  (g : iso-Precategory C y z)
  (f : iso-Precategory C x y)
  where

  associative-comp-iso-Precategory :
    ( comp-iso-Precategory C (comp-iso-Precategory C h g) f) ＝
    ( comp-iso-Precategory C h (comp-iso-Precategory C g f))
  associative-comp-iso-Precategory =
    eq-iso-eq-hom-Precategory C
      ( comp-iso-Precategory C (comp-iso-Precategory C h g) f)
      ( comp-iso-Precategory C h (comp-iso-Precategory C g f))
      ( associative-comp-hom-Precategory C
        ( hom-iso-Precategory C h)
        ( hom-iso-Precategory C g)
        ( hom-iso-Precategory C f))
```

#### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : iso-Precategory C x y)
  where

  left-inverse-law-comp-iso-Precategory :
    ( comp-iso-Precategory C (inv-iso-Precategory C f) f) ＝
    ( id-iso-Precategory C)
  left-inverse-law-comp-iso-Precategory =
    eq-iso-eq-hom-Precategory C
      ( comp-iso-Precategory C (inv-iso-Precategory C f) f)
      ( id-iso-Precategory C)
      ( is-retraction-hom-inv-iso-Precategory C f)

  right-inverse-law-comp-iso-Precategory :
    ( comp-iso-Precategory C f (inv-iso-Precategory C f)) ＝
    ( id-iso-Precategory C)
  right-inverse-law-comp-iso-Precategory =
    eq-iso-eq-hom-Precategory C
      ( comp-iso-Precategory C f (inv-iso-Precategory C f))
      ( id-iso-Precategory C)
      ( is-section-hom-inv-iso-Precategory C f)
```

### A morphism `f` is an isomorphism if and only if precomposition by `f` is an equivalence

**Proof:** If `f` is an isomorphism with inverse `f⁻¹`, then precomposing with
`f⁻¹` is an inverse of precomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that precomposing with `f` is an equivalence, for any object `z`. Then

```text
  - ∘ f : hom y x → hom x x
```

is an equivalence. In particular, there is a unique morphism `g : y → x` such
that `g ∘ f ＝ id`. Thus we have a retraction of `f`. To see that `g` is also a
section, note that the map

```text
  - ∘ f : hom y y → hom x y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `(f ∘ g) ∘ f ＝ id ∘ f`. To see this, we calculate

```text
  (f ∘ g) ∘ f ＝ f ∘ (g ∘ f) ＝ f ∘ id ＝ f ＝ id ∘ f.
```

This completes the proof.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (H : (z : obj-Precategory C) → is-equiv (precomp-hom-Precategory C f z))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Precategory : hom-Precategory C y x
  hom-inv-is-iso-is-equiv-precomp-hom-Precategory =
    map-inv-is-equiv (H x) (id-hom-Precategory C)

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-is-iso-is-equiv-precomp-hom-Precategory)
      ( f)) ＝
    ( id-hom-Precategory C)
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategory =
    is-section-map-inv-is-equiv (H x) (id-hom-Precategory C)

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategory :
    ( comp-hom-Precategory C
      ( f)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategory =
    is-injective-is-equiv
      ( H y)
      ( ( associative-comp-hom-Precategory C
          ( f)
          ( hom-inv-is-iso-is-equiv-precomp-hom-Precategory)
          ( f)) ∙
        ( ap
          ( comp-hom-Precategory C f)
          ( is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategory)) ∙
        ( right-unit-law-comp-hom-Precategory C f) ∙
        ( inv (left-unit-law-comp-hom-Precategory C f)))

  is-iso-is-equiv-precomp-hom-Precategory : is-iso-Precategory C f
  pr1 is-iso-is-equiv-precomp-hom-Precategory =
    hom-inv-is-iso-is-equiv-precomp-hom-Precategory
  pr1 (pr2 is-iso-is-equiv-precomp-hom-Precategory) =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategory
  pr2 (pr2 is-iso-is-equiv-precomp-hom-Precategory) =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategory
```

### A morphism `f` is an isomorphism if and only if postcomposition by `f` is an equivalence

**Proof:** If `f` is an isomorphism with inverse `f⁻¹`, then postcomposing with
`f⁻¹` is an inverse of postcomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that postcomposing with `f` is an equivalence, for any object `z`. Then

```text
  f ∘ - : hom y x → hom y y
```

is an equivalence. In particular, there is a unique morphism `g : y → x` such
that `f ∘ g ＝ id`. Thus we have a section of `f`. To see that `g` is also a
retraction, note that the map

```text
  f ∘ - : hom x x → hom x y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `f ∘ (g ∘ f) ＝ f ∘ id`. To see this, we calculate

```text
  f ∘ (g ∘ f) ＝ (f ∘ g) ∘ f ＝ id ∘ f ＝ f ＝ f ∘ id.
```

This completes the proof.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (H : (z : obj-Precategory C) → is-equiv (postcomp-hom-Precategory C f z))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Precategory : hom-Precategory C y x
  hom-inv-is-iso-is-equiv-postcomp-hom-Precategory =
    map-inv-is-equiv (H y) (id-hom-Precategory C)

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory :
    ( comp-hom-Precategory C
      ( f)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory =
    is-section-map-inv-is-equiv (H y) (id-hom-Precategory C)

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategory))
      ( f) ＝
    ( id-hom-Precategory C)
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory =
    is-injective-is-equiv
      ( H x)
      ( ( inv
          ( associative-comp-hom-Precategory C
            ( f)
            ( hom-inv-is-iso-is-equiv-postcomp-hom-Precategory)
            ( f))) ∙
        ( ap
          ( comp-hom-Precategory' C f)
          ( is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory)) ∙
        ( left-unit-law-comp-hom-Precategory C f) ∙
        ( inv (right-unit-law-comp-hom-Precategory C f)))

  is-iso-is-equiv-postcomp-hom-Precategory : is-iso-Precategory C f
  pr1 is-iso-is-equiv-postcomp-hom-Precategory =
    hom-inv-is-iso-is-equiv-postcomp-hom-Precategory
  pr1 (pr2 is-iso-is-equiv-postcomp-hom-Precategory) =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory
  pr2 (pr2 is-iso-is-equiv-postcomp-hom-Precategory) =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory
```

### When `hom x y` is a proposition, The type of isomorphisms from `x` to `y` is a proposition

The type of isomorphisms between objects `x y : A` is a subtype of `hom x y`, so
when this type is a proposition, then the type of isomorphisms from `x` to `y`
form a proposition.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-prop-iso-Precategory :
    is-prop (hom-Precategory C x y) → is-prop (iso-Precategory C x y)
  is-prop-iso-Precategory = is-prop-type-subtype (is-iso-prop-Precategory C)

  iso-prop-Precategory :
    is-prop (hom-Precategory C x y) → Prop l2
  pr1 (iso-prop-Precategory _) = iso-Precategory C x y
  pr2 (iso-prop-Precategory is-prop-hom-C-x-y) =
    is-prop-iso-Precategory is-prop-hom-C-x-y
```

### When `hom x y` and `hom y x` are propositions, it suffices to provide a homomorphism in each direction to construct an isomorphism

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-iso-is-prop-hom-Precategory' :
    is-prop (hom-Precategory C x x) →
    is-prop (hom-Precategory C y y) →
    (f : hom-Precategory C x y) →
    hom-Precategory C y x →
    is-iso-Precategory C f
  pr1 (is-iso-is-prop-hom-Precategory' _ _ f g) = g
  pr1 (pr2 (is-iso-is-prop-hom-Precategory' _ is-prop-hom-C-y-y f g)) =
    eq-is-prop is-prop-hom-C-y-y
  pr2 (pr2 (is-iso-is-prop-hom-Precategory' is-prop-hom-C-x-x _ f g)) =
    eq-is-prop is-prop-hom-C-x-x

  iso-is-prop-hom-Precategory' :
    is-prop (hom-Precategory C x x) →
    is-prop (hom-Precategory C y y) →
    hom-Precategory C x y →
    hom-Precategory C y x →
    iso-Precategory C x y
  pr1 (iso-is-prop-hom-Precategory' _ _ f g) = f
  pr2 (iso-is-prop-hom-Precategory' is-prop-hom-C-x-x is-prop-hom-C-y-y f g) =
    is-iso-is-prop-hom-Precategory' is-prop-hom-C-x-x is-prop-hom-C-y-y f g

  is-iso-is-prop-hom-Precategory :
    ((x' y' : obj-Precategory C) → is-prop (hom-Precategory C x' y')) →
    (f : hom-Precategory C x y) → hom-Precategory C y x →
    is-iso-Precategory C f
  is-iso-is-prop-hom-Precategory is-prop-hom-C =
    is-iso-is-prop-hom-Precategory' (is-prop-hom-C x x) (is-prop-hom-C y y)

  iso-is-prop-hom-Precategory :
    ((x' y' : obj-Precategory C) → is-prop (hom-Precategory C x' y')) →
    hom-Precategory C x y →
    hom-Precategory C y x →
    iso-Precategory C x y
  iso-is-prop-hom-Precategory is-prop-hom-C =
    iso-is-prop-hom-Precategory' (is-prop-hom-C x x) (is-prop-hom-C y y)
```

### Functoriality of `iso-eq`

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  where

  preserves-concat-iso-eq-Precategory :
    (p : x ＝ y) (q : y ＝ z) →
    iso-eq-Precategory C x z (p ∙ q) ＝
    comp-iso-Precategory C
      ( iso-eq-Precategory C y z q)
      ( iso-eq-Precategory C x y p)
  preserves-concat-iso-eq-Precategory refl q =
    inv (right-unit-law-comp-iso-Precategory C (iso-eq-Precategory C y z q))
```
