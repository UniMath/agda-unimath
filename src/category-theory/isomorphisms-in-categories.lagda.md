# Isomorphisms in categories

```agda
module category-theory.isomorphisms-in-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

An **isomorphism** in a [category](category-theory.categories.md) `C` is a
morphism `f : x → y` in `C` for which there exists a morphism `g : y → x` such
that `f ∘ g ＝ id` and `g ∘ f ＝ id`.

## Definitions

### The predicate of being an isomorphism in a category

```agda
is-iso-Category :
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  (f : hom-Category C x y) →
  UU l2
is-iso-Category C = is-iso-Precategory (precategory-Category C)

module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  {f : hom-Category C x y}
  where

  hom-inv-is-iso-Category :
    is-iso-Category C f → hom-Category C y x
  hom-inv-is-iso-Category =
    hom-inv-is-iso-Precategory (precategory-Category C)

  is-section-hom-inv-is-iso-Category :
    (H : is-iso-Category C f) →
    comp-hom-Category C f (hom-inv-is-iso-Category H) ＝
    id-hom-Category C
  is-section-hom-inv-is-iso-Category =
    is-section-hom-inv-is-iso-Precategory (precategory-Category C)

  is-retraction-hom-inv-is-iso-Category :
    (H : is-iso-Category C f) →
    comp-hom-Category C (hom-inv-is-iso-Category H) f ＝
    id-hom-Category C
  is-retraction-hom-inv-is-iso-Category =
    is-retraction-hom-inv-is-iso-Precategory (precategory-Category C)
```

### Isomorphisms in a category

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  (x y : obj-Category C)
  where

  iso-Category : UU l2
  iso-Category = iso-Precategory (precategory-Category C) x y

module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  (f : iso-Category C x y)
  where

  hom-iso-Category : hom-Category C x y
  hom-iso-Category = hom-iso-Precategory (precategory-Category C) f

  is-iso-iso-Category :
    is-iso-Category C hom-iso-Category
  is-iso-iso-Category =
    is-iso-iso-Precategory (precategory-Category C) f

  hom-inv-iso-Category : hom-Category C y x
  hom-inv-iso-Category = hom-inv-iso-Precategory (precategory-Category C) f

  is-section-hom-inv-iso-Category :
    ( comp-hom-Category C
      ( hom-iso-Category)
      ( hom-inv-iso-Category)) ＝
    ( id-hom-Category C)
  is-section-hom-inv-iso-Category =
    is-section-hom-inv-iso-Precategory (precategory-Category C) f

  is-retraction-hom-inv-iso-Category :
    ( comp-hom-Category C
      ( hom-inv-iso-Category)
      ( hom-iso-Category)) ＝
    ( id-hom-Category C)
  is-retraction-hom-inv-iso-Category =
    is-retraction-hom-inv-iso-Precategory (precategory-Category C) f
```

## Examples

### The identity isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = id_x` (it is its own inverse).

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x : obj-Category C}
  where

  is-iso-id-hom-Category : is-iso-Category C (id-hom-Category C {x})
  is-iso-id-hom-Category = is-iso-id-hom-Precategory (precategory-Category C)

  id-iso-Category : iso-Category C x x
  id-iso-Category = id-iso-Precategory (precategory-Category C)
```

### Equalities induce isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because, by the J-rule, it is enough to construct an isomorphism given
`refl : x ＝ x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  iso-eq-Category :
    (x y : obj-Category C) →
    x ＝ y → iso-Category C x y
  iso-eq-Category = iso-eq-Precategory (precategory-Category C)

  compute-hom-iso-eq-Category :
    {x y : obj-Category C} →
    (p : x ＝ y) →
    hom-eq-Category C x y p ＝
    hom-iso-Category C (iso-eq-Category x y p)
  compute-hom-iso-eq-Category =
    compute-hom-iso-eq-Precategory (precategory-Category C)
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
  (C : Category l1 l2)
  {x y : obj-Category C}
  where

  is-prop-is-iso-Category :
    (f : hom-Category C x y) → is-prop (is-iso-Category C f)
  is-prop-is-iso-Category =
    is-prop-is-iso-Precategory (precategory-Category C)

  is-iso-prop-Category :
    (f : hom-Category C x y) → Prop l2
  is-iso-prop-Category =
    is-iso-prop-Precategory (precategory-Category C)
```

### Equality of isomorphism is equality of their underlying morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  where

  eq-iso-eq-hom-Category :
    (f g : iso-Category C x y) →
    hom-iso-Category C f ＝ hom-iso-Category C g → f ＝ g
  eq-iso-eq-hom-Category =
    eq-iso-eq-hom-Precategory (precategory-Category C)
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a
[subtype](foundation-core.subtypes.md) of the [foundation-core.sets.md)
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  where

  is-set-iso-Category : is-set (iso-Category C x y)
  is-set-iso-Category = is-set-iso-Precategory (precategory-Category C)

  iso-set-Category : Set l2
  pr1 iso-set-Category = iso-Category C x y
  pr2 iso-set-Category = is-set-iso-Category
```

### Isomorphisms are closed under composition

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y z : obj-Category C}
  {g : hom-Category C y z}
  {f : hom-Category C x y}
  where

  hom-comp-is-iso-Category :
    is-iso-Category C g →
    is-iso-Category C f →
    hom-Category C z x
  hom-comp-is-iso-Category =
    hom-comp-is-iso-Precategory (precategory-Category C)

  is-section-comp-is-iso-Category :
    (q : is-iso-Category C g)
    (p : is-iso-Category C f) →
    comp-hom-Category C
      ( comp-hom-Category C g f)
      ( hom-comp-is-iso-Category q p) ＝
    id-hom-Category C
  is-section-comp-is-iso-Category =
    is-section-comp-is-iso-Precategory (precategory-Category C)

  is-retraction-comp-is-iso-Category :
    (q : is-iso-Category C g)
    (p : is-iso-Category C f) →
    ( comp-hom-Category C
      ( hom-comp-is-iso-Category q p)
      ( comp-hom-Category C g f)) ＝
    ( id-hom-Category C)
  is-retraction-comp-is-iso-Category =
    is-retraction-comp-is-iso-Precategory (precategory-Category C)

  is-iso-comp-is-iso-Category :
    is-iso-Category C g → is-iso-Category C f →
    is-iso-Category C (comp-hom-Category C g f)
  is-iso-comp-is-iso-Category =
    is-iso-comp-is-iso-Precategory (precategory-Category C)
```

### Composition of isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y z : obj-Category C}
  (g : iso-Category C y z)
  (f : iso-Category C x y)
  where

  hom-comp-iso-Category : hom-Category C x z
  hom-comp-iso-Category = hom-comp-iso-Precategory (precategory-Category C) g f

  is-iso-comp-iso-Category :
    is-iso-Category C hom-comp-iso-Category
  is-iso-comp-iso-Category =
    is-iso-comp-iso-Precategory (precategory-Category C) g f

  comp-iso-Category : iso-Category C x z
  comp-iso-Category = comp-iso-Precategory (precategory-Category C) g f

  hom-inv-comp-iso-Category : hom-Category C z x
  hom-inv-comp-iso-Category =
    hom-inv-comp-iso-Precategory (precategory-Category C) g f

  is-section-inv-comp-iso-Category :
    ( comp-hom-Category C
      ( hom-comp-iso-Category)
      ( hom-inv-comp-iso-Category)) ＝
    ( id-hom-Category C)
  is-section-inv-comp-iso-Category =
    is-section-inv-comp-iso-Precategory (precategory-Category C) g f

  is-retraction-inv-comp-iso-Category :
    ( comp-hom-Category C
      ( hom-inv-comp-iso-Category)
      ( hom-comp-iso-Category)) ＝
    ( id-hom-Category C)
  is-retraction-inv-comp-iso-Category =
    is-retraction-inv-comp-iso-Precategory (precategory-Category C) g f
```

### Inverses of isomorphisms are isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  {f : hom-Category C x y}
  where

  is-iso-inv-is-iso-Category :
    (p : is-iso-Category C f) →
    is-iso-Category C (hom-inv-iso-Category C (f , p))
  is-iso-inv-is-iso-Category =
    is-iso-inv-is-iso-Precategory (precategory-Category C)
```

### Inverses of isomorphisms

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  where

  inv-iso-Category :
    iso-Category C x y → iso-Category C y x
  inv-iso-Category = inv-iso-Precategory (precategory-Category C)
```

### Groupoid laws of isomorphisms in categories

#### Composition of isomorphisms satisfies the unit laws

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  (f : iso-Category C x y)
  where

  left-unit-law-comp-iso-Category :
    comp-iso-Category C (id-iso-Category C) f ＝ f
  left-unit-law-comp-iso-Category =
    left-unit-law-comp-iso-Precategory (precategory-Category C) f

  right-unit-law-comp-iso-Category :
    comp-iso-Category C f (id-iso-Category C) ＝ f
  right-unit-law-comp-iso-Category =
    right-unit-law-comp-iso-Precategory (precategory-Category C) f
```

#### Composition of isomorphisms is associative

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y z w : obj-Category C}
  (h : iso-Category C z w)
  (g : iso-Category C y z)
  (f : iso-Category C x y)
  where

  associative-comp-iso-Category :
    ( comp-iso-Category C (comp-iso-Category C h g) f) ＝
    ( comp-iso-Category C h (comp-iso-Category C g f))
  associative-comp-iso-Category =
    associative-comp-iso-Precategory (precategory-Category C) h g f
```

#### Composition of isomorphisms satisfies inverse laws

```agda
module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  (f : iso-Category C x y)
  where

  left-inverse-law-comp-iso-Category :
    ( comp-iso-Category C (inv-iso-Category C f) f) ＝
    ( id-iso-Category C)
  left-inverse-law-comp-iso-Category =
    left-inverse-law-comp-iso-Precategory (precategory-Category C) f

  right-inverse-law-comp-iso-Category :
    ( comp-iso-Category C f (inv-iso-Category C f)) ＝
    ( id-iso-Category C)
  right-inverse-law-comp-iso-Category =
    right-inverse-law-comp-iso-Precategory (precategory-Category C) f
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
  (C : Category l1 l2)
  {x y : obj-Category C}
  {f : hom-Category C x y}
  (H : (z : obj-Category C) → is-equiv (precomp-hom-Category C f z))
  where

  hom-inv-is-iso-is-equiv-precomp-hom-Category : hom-Category C y x
  hom-inv-is-iso-is-equiv-precomp-hom-Category =
    hom-inv-is-iso-is-equiv-precomp-hom-Precategory (precategory-Category C) H

  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Category :
    ( comp-hom-Category C
      ( hom-inv-is-iso-is-equiv-precomp-hom-Category)
      ( f)) ＝
    ( id-hom-Category C)
  is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Category =
    is-retraction-hom-inv-is-iso-is-equiv-precomp-hom-Precategory
      ( precategory-Category C) H

  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Category :
    ( comp-hom-Category C
      ( f)
      ( hom-inv-is-iso-is-equiv-precomp-hom-Category)) ＝
    ( id-hom-Category C)
  is-section-hom-inv-is-iso-is-equiv-precomp-hom-Category =
    is-section-hom-inv-is-iso-is-equiv-precomp-hom-Precategory
      ( precategory-Category C) H

  is-iso-is-equiv-precomp-hom-Category : is-iso-Category C f
  is-iso-is-equiv-precomp-hom-Category =
    is-iso-is-equiv-precomp-hom-Precategory (precategory-Category C) H

module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  {f : hom-Category C x y}
  (is-iso-f : is-iso-Category C f)
  (z : obj-Category C)
  where

  map-inv-precomp-hom-is-iso-Category : hom-Category C x z → hom-Category C y z
  map-inv-precomp-hom-is-iso-Category =
    precomp-hom-Category C (hom-inv-is-iso-Category C is-iso-f) z

  is-equiv-precomp-hom-is-iso-Category : is-equiv (precomp-hom-Category C f z)
  is-equiv-precomp-hom-is-iso-Category =
    is-equiv-precomp-hom-is-iso-Precategory (precategory-Category C) is-iso-f z

  equiv-precomp-hom-is-iso-Category : hom-Category C y z ≃ hom-Category C x z
  equiv-precomp-hom-is-iso-Category =
    equiv-precomp-hom-is-iso-Precategory (precategory-Category C) is-iso-f z

module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  (f : iso-Category C x y)
  (z : obj-Category C)
  where

  is-equiv-precomp-hom-iso-Category :
    is-equiv (precomp-hom-Category C (hom-iso-Category C f) z)
  is-equiv-precomp-hom-iso-Category =
    is-equiv-precomp-hom-is-iso-Category C (is-iso-iso-Category C f) z

  equiv-precomp-hom-iso-Category :
    hom-Category C y z ≃ hom-Category C x z
  equiv-precomp-hom-iso-Category =
    equiv-precomp-hom-is-iso-Category C (is-iso-iso-Category C f) z
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
  (C : Category l1 l2)
  {x y : obj-Category C}
  {f : hom-Category C x y}
  (H : (z : obj-Category C) → is-equiv (postcomp-hom-Category C f z))
  where

  hom-inv-is-iso-is-equiv-postcomp-hom-Category : hom-Category C y x
  hom-inv-is-iso-is-equiv-postcomp-hom-Category =
    hom-inv-is-iso-is-equiv-postcomp-hom-Precategory (precategory-Category C) H

  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Category :
    ( comp-hom-Category C
      ( f)
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Category)) ＝
    ( id-hom-Category C)
  is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Category =
    is-section-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory
      ( precategory-Category C) H

  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Category :
    comp-hom-Category C
      ( hom-inv-is-iso-is-equiv-postcomp-hom-Category)
      ( f) ＝
    ( id-hom-Category C)
  is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Category =
    is-retraction-hom-inv-is-iso-is-equiv-postcomp-hom-Precategory
      ( precategory-Category C) H

  is-iso-is-equiv-postcomp-hom-Category : is-iso-Category C f
  is-iso-is-equiv-postcomp-hom-Category =
    is-iso-is-equiv-postcomp-hom-Precategory
      ( precategory-Category C) H

module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  {f : hom-Category C x y}
  (is-iso-f : is-iso-Category C f)
  (z : obj-Category C)
  where

  map-inv-postcomp-hom-is-iso-Category : hom-Category C z y → hom-Category C z x
  map-inv-postcomp-hom-is-iso-Category =
    postcomp-hom-Category C (hom-inv-is-iso-Category C is-iso-f) z

  is-equiv-postcomp-hom-is-iso-Category : is-equiv (postcomp-hom-Category C f z)
  is-equiv-postcomp-hom-is-iso-Category =
    is-equiv-postcomp-hom-is-iso-Precategory (precategory-Category C) is-iso-f z

  equiv-postcomp-hom-is-iso-Category : hom-Category C z x ≃ hom-Category C z y
  equiv-postcomp-hom-is-iso-Category =
    equiv-postcomp-hom-is-iso-Precategory (precategory-Category C) is-iso-f z

module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  {x y : obj-Category C}
  (f : iso-Category C x y)
  (z : obj-Category C)
  where

  is-equiv-postcomp-hom-iso-Category :
    is-equiv (postcomp-hom-Category C (hom-iso-Category C f) z)
  is-equiv-postcomp-hom-iso-Category =
    is-equiv-postcomp-hom-is-iso-Category C (is-iso-iso-Category C f) z

  equiv-postcomp-hom-iso-Category : hom-Category C z x ≃ hom-Category C z y
  equiv-postcomp-hom-iso-Category =
    equiv-postcomp-hom-is-iso-Category C (is-iso-iso-Category C f) z
```

### When `hom x y` is a proposition, the type of isomorphisms from `x` to `y` is a proposition

The type of isomorphisms between objects `x y : A` is a subtype of `hom x y`, so
when this type is a proposition, then the type of isomorphisms from `x` to `y`
form a proposition.

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  {x y : obj-Category C}
  where

  is-prop-iso-is-prop-hom-Category :
    is-prop (hom-Category C x y) → is-prop (iso-Category C x y)
  is-prop-iso-is-prop-hom-Category =
    is-prop-iso-is-prop-hom-Precategory (precategory-Category C)

  iso-prop-is-prop-hom-Category :
    is-prop (hom-Category C x y) → Prop l2
  iso-prop-is-prop-hom-Category =
    iso-prop-is-prop-hom-Precategory (precategory-Category C)
```

### When `hom x y` and `hom y x` are propositions, it suffices to provide a morphism in each direction to construct an isomorphism

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  {x y : obj-Category C}
  where

  is-iso-is-prop-hom-Category' :
    is-prop (hom-Category C x x) →
    is-prop (hom-Category C y y) →
    (f : hom-Category C x y) →
    hom-Category C y x →
    is-iso-Category C f
  is-iso-is-prop-hom-Category' =
    is-iso-is-prop-hom-Precategory' (precategory-Category C)

  iso-is-prop-hom-Category' :
    is-prop (hom-Category C x x) →
    is-prop (hom-Category C y y) →
    hom-Category C x y →
    hom-Category C y x →
    iso-Category C x y
  iso-is-prop-hom-Category' =
    iso-is-prop-hom-Precategory' (precategory-Category C)

  is-iso-is-prop-hom-Category :
    ((x' y' : obj-Category C) → is-prop (hom-Category C x' y')) →
    (f : hom-Category C x y) → hom-Category C y x →
    is-iso-Category C f
  is-iso-is-prop-hom-Category =
    is-iso-is-prop-hom-Precategory (precategory-Category C)

  iso-is-prop-hom-Category :
    ((x' y' : obj-Category C) → is-prop (hom-Category C x' y')) →
    hom-Category C x y →
    hom-Category C y x →
    iso-Category C x y
  iso-is-prop-hom-Category =
    iso-is-prop-hom-Precategory (precategory-Category C)
```

### Functoriality of `iso-eq`

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  {x y z : obj-Category C}
  where

  preserves-concat-iso-eq-Category :
    (p : x ＝ y) (q : y ＝ z) →
    iso-eq-Category C x z (p ∙ q) ＝
    comp-iso-Category C (iso-eq-Category C y z q) (iso-eq-Category C x y p)
  preserves-concat-iso-eq-Category =
    preserves-concat-iso-eq-Precategory (precategory-Category C)
```

### Extensionality of the type of objects in a category

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  extensionality-obj-Category :
    (x y : obj-Category C) → (x ＝ y) ≃ iso-Category C x y
  pr1 (extensionality-obj-Category x y) = iso-eq-Category C x y
  pr2 (extensionality-obj-Category x y) = is-category-Category C x y

  eq-iso-Category :
    {x y : obj-Category C} → iso-Category C x y → x ＝ y
  eq-iso-Category {x} {y} = map-inv-equiv (extensionality-obj-Category x y)

  is-section-eq-iso-Category :
    {x y : obj-Category C} (f : iso-Category C x y) →
    iso-eq-Category C x y (eq-iso-Category f) ＝ f
  is-section-eq-iso-Category {x} {y} =
    is-section-map-inv-equiv (extensionality-obj-Category x y)

  is-retraction-eq-iso-Category :
    {x y : obj-Category C} (p : x ＝ y) →
    eq-iso-Category (iso-eq-Category C x y p) ＝ p
  is-retraction-eq-iso-Category {x} {y} =
    is-retraction-map-inv-equiv (extensionality-obj-Category x y)

module _
  {l1 l2 : Level}
  (C : Category l1 l2)
  (X : obj-Category C)
  where

  is-torsorial-iso-Category :
    is-torsorial (iso-Category C X)
  is-torsorial-iso-Category =
    is-contr-equiv'
      ( Σ (obj-Category C) (X ＝_))
      ( equiv-tot (extensionality-obj-Category C X))
      ( is-torsorial-path X)

  is-torsorial-iso-Category' :
    is-torsorial (λ Y → iso-Category C Y X)
  is-torsorial-iso-Category' =
    is-contr-equiv'
      ( Σ (obj-Category C) (_＝ X))
      ( equiv-tot (λ Y → extensionality-obj-Category C Y X))
      ( is-torsorial-path' X)
```

### Functoriality of `eq-iso`

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  preserves-comp-eq-iso-Category :
    { x y z : obj-Category C}
    ( g : iso-Category C y z)
    ( f : iso-Category C x y) →
    ( eq-iso-Category C (comp-iso-Category C g f)) ＝
    ( eq-iso-Category C f ∙ eq-iso-Category C g)
  preserves-comp-eq-iso-Category g f =
    ( ap
      ( eq-iso-Category C)
      ( ap-binary
        ( comp-iso-Category C)
        ( inv (is-section-eq-iso-Category C g))
        ( inv (is-section-eq-iso-Category C f)))) ∙
    ( ap
      ( eq-iso-Category C)
      ( inv
        ( preserves-concat-iso-eq-Category C
          ( eq-iso-Category C f)
          ( eq-iso-Category C g)))) ∙
    ( is-retraction-eq-iso-Category C
      ( eq-iso-Category C f ∙ eq-iso-Category C g))
```
