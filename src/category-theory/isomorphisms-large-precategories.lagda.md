# Isomorphisms in large precategories

```agda
module category-theory.isomorphisms-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

An isomorphism between objects `x y : A` in a precategory `C` is a morphism `f : hom x y` for which there exists a morphism `g : hom y x` such that
- `comp g f = id_x` and
- `comp f g = id_y`.

## Definition

```agda
is-iso-Large-Precat :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precat α β) {l1 l2 : Level} →
  {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2} →
  type-hom-Large-Precat C X Y → UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
is-iso-Large-Precat C {X = X} {Y = Y} f =
  Σ ( type-hom-Large-Precat C Y X)
    ( λ g →
      ( comp-hom-Large-Precat C f g ＝ id-hom-Large-Precat C) ×
      ( comp-hom-Large-Precat C g f ＝ id-hom-Large-Precat C))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  iso-Large-Precat : UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  iso-Large-Precat =
    Σ (type-hom-Large-Precat C X Y) (is-iso-Large-Precat C)

  hom-iso-Large-Precat : iso-Large-Precat → type-hom-Large-Precat C X Y
  hom-iso-Large-Precat = pr1

  is-iso-hom-iso-Large-Precat :
    (f : iso-Large-Precat) →
    is-iso-Large-Precat C (hom-iso-Large-Precat f)
  is-iso-hom-iso-Large-Precat f = pr2 f

  hom-inv-iso-Large-Precat : iso-Large-Precat → type-hom-Large-Precat C Y X
  hom-inv-iso-Large-Precat f = pr1 (pr2 f)

  is-sec-hom-inv-iso-Large-Precat :
    (f : iso-Large-Precat) →
    ( comp-hom-Large-Precat C
      ( hom-iso-Large-Precat f)
      ( hom-inv-iso-Large-Precat f)) ＝
    ( id-hom-Large-Precat C)
  is-sec-hom-inv-iso-Large-Precat f = pr1 (pr2 (pr2 f))

  is-retr-hom-inv-iso-Large-Precat :
    (f : iso-Large-Precat) →
    ( comp-hom-Large-Precat C
      ( hom-inv-iso-Large-Precat f)
      ( hom-iso-Large-Precat f)) ＝
    ( id-hom-Large-Precat C)
  is-retr-hom-inv-iso-Large-Precat f = pr2 (pr2 (pr2 f))
```

## Examples

### The identity morphisms are isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism from `x` to `x` since `comp id_x id_x = id_x` (it is its own inverse).

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 : Level} {X : obj-Large-Precat C l1}
  where

  id-iso-Large-Precat : iso-Large-Precat C X X
  pr1 id-iso-Large-Precat = id-hom-Large-Precat C
  pr1 (pr2 id-iso-Large-Precat) = id-hom-Large-Precat C
  pr1 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)
  pr2 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-hom-Large-Precat C (id-hom-Large-Precat C)
```

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them. This is because by the J-rule, it is enough to construct an isomorphism given `refl : Id x x`, from `x` to itself. We take the identity morphism as such an isomorphism.

```agda
iso-eq-Large-Precat :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precat α β) {l1 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l1) →
  X ＝ Y → iso-Large-Precat C X Y
iso-eq-Large-Precat C X .X refl = id-iso-Large-Precat C
```

## Properties

### Being an isomorphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both two-sided inverses to `f`. It is enough to show that `g = g'` since the equalities are propositions (since the hom-types are sets). But we have the following chain of equalities:
`g = comp g id_y
   = comp g (comp f g')
   = comp (comp g f) g'
   = comp id_x g'
   = g'.`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  all-elements-equal-is-iso-Large-Precat :
    (f : type-hom-Large-Precat C X Y)
    (H K : is-iso-Large-Precat C f) → H ＝ K
  all-elements-equal-is-iso-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-type-subtype
      ( λ g →
        prod-Prop
          ( Id-Prop
            ( hom-Large-Precat C Y Y)
            ( comp-hom-Large-Precat C f g)
            ( id-hom-Large-Precat C))
          ( Id-Prop
            ( hom-Large-Precat C X X)
            ( comp-hom-Large-Precat C g f)
            ( id-hom-Large-Precat C)))
      ( ( inv (right-unit-law-comp-hom-Large-Precat C g)) ∙
        ( ( ap ( comp-hom-Large-Precat C g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Large-Precat C g f g')) ∙
            ( ( ap ( comp-hom-Large-Precat' C g') q) ∙
              ( left-unit-law-comp-hom-Large-Precat C g')))))

  is-prop-is-iso-Large-Precat :
    (f : type-hom-Large-Precat C X Y) → is-prop (is-iso-Large-Precat C f)
  is-prop-is-iso-Large-Precat f =
    is-prop-all-elements-equal (all-elements-equal-is-iso-Large-Precat f)

  is-iso-large-precat-Prop :
    (f : type-hom-Large-Precat C X Y) → Prop (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 (is-iso-large-precat-Prop f) = is-iso-Large-Precat C f
  pr2 (is-iso-large-precat-Prop f) = is-prop-is-iso-Large-Precat f
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set `hom x y` since being an isomorphism is a proposition.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  is-set-iso-Large-Precat : is-set (iso-Large-Precat C X Y)
  is-set-iso-Large-Precat =
    is-set-type-subtype
      ( is-iso-large-precat-Prop C X Y)
      ( is-set-type-hom-Large-Precat C X Y)

  iso-Large-Precat-Set : Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Large-Precat-Set = iso-Large-Precat C X Y
  pr2 iso-Large-Precat-Set = is-set-iso-Large-Precat
```

### Isomorphisms are stable by composition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 l3 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  (Z : obj-Large-Precat C l3)
  where

  is-iso-comp-iso-Large-Precat : (g : type-hom-Large-Precat C Y Z) →
    (f : type-hom-Large-Precat C X Y) →
    is-iso-Large-Precat C g → is-iso-Large-Precat C f →
    is-iso-Large-Precat C (comp-hom-Large-Precat C g f)
  pr1 (is-iso-comp-iso-Large-Precat g f q p) =
    comp-hom-Large-Precat C
      ( hom-inv-iso-Large-Precat C X Y (pair f p))
      ( hom-inv-iso-Large-Precat C Y Z (pair g q))
  pr1 (pr2 (is-iso-comp-iso-Large-Precat g f q p)) =
    ( associative-comp-hom-Large-Precat C g f (pr1 (is-iso-comp-iso-Large-Precat g f q p))) ∙
      ( ( ap
        ( comp-hom-Large-Precat C g)
        ( ( inv
          ( associative-comp-hom-Large-Precat C f
            ( hom-inv-iso-Large-Precat C X Y (pair f p))
            ( hom-inv-iso-Large-Precat C Y Z (pair g q)))) ∙
          ( ( ap
            ( λ h →
              comp-hom-Large-Precat C h
                (hom-inv-iso-Large-Precat C Y Z (pair g q)))
            ( is-sec-hom-inv-iso-Large-Precat C X Y (pair f p))) ∙
            ( left-unit-law-comp-hom-Large-Precat C
              ( hom-inv-iso-Large-Precat C Y Z (pair g q)))))) ∙
        ( is-sec-hom-inv-iso-Large-Precat C Y Z (pair g q)))
  pr2 (pr2 (is-iso-comp-iso-Large-Precat g f q p)) =
    ( associative-comp-hom-Large-Precat C
      ( hom-inv-iso-Large-Precat C X Y (pair f p))
      ( hom-inv-iso-Large-Precat C Y Z (pair g q))
      ( comp-hom-Large-Precat C g f)) ∙
      ( ( ap
        ( comp-hom-Large-Precat C (hom-inv-iso-Large-Precat C X Y (pair f p)))
        ( ( inv
          ( associative-comp-hom-Large-Precat C
            ( hom-inv-iso-Large-Precat C Y Z (pair g q))
            ( g)
            ( f))) ∙
          ( ( ap
            ( λ h → comp-hom-Large-Precat C h f)
            ( is-retr-hom-inv-iso-Large-Precat C Y Z (pair g q))) ∙
            ( left-unit-law-comp-hom-Large-Precat C f)))) ∙
        ( is-retr-hom-inv-iso-Large-Precat C X Y (pair f p)))

  comp-iso-Large-Precat : iso-Large-Precat C Y Z →
    iso-Large-Precat C X Y →
    iso-Large-Precat C X Z
  pr1 (comp-iso-Large-Precat g f) =
    comp-hom-Large-Precat C
      ( hom-iso-Large-Precat C Y Z g)
      ( hom-iso-Large-Precat C X Y f)
  pr2 (comp-iso-Large-Precat f g) =
    is-iso-comp-iso-Large-Precat
      ( hom-iso-Large-Precat C Y Z f)
      ( hom-iso-Large-Precat C X Y g)
      ( is-iso-hom-iso-Large-Precat C Y Z f)
      ( is-iso-hom-iso-Large-Precat C X Y g)
```

### Isomorphisms are stable by inversion

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  is-iso-inv-iso-Large-Precat : (f : type-hom-Large-Precat C X Y) →
    (p : is-iso-Large-Precat C f) →
    is-iso-Large-Precat C (hom-inv-iso-Large-Precat C X Y (pair f p))
  pr1 (is-iso-inv-iso-Large-Precat f p) = f
  pr1 (pr2 (is-iso-inv-iso-Large-Precat f p)) =
    is-retr-hom-inv-iso-Large-Precat C X Y (pair f p)
  pr2 (pr2 (is-iso-inv-iso-Large-Precat f p)) =
    is-sec-hom-inv-iso-Large-Precat C X Y (pair f p)

  inv-iso-Large-Precat : iso-Large-Precat C X Y →
    iso-Large-Precat C Y X
  pr1 (inv-iso-Large-Precat f) = hom-inv-iso-Large-Precat C X Y f
  pr2 (inv-iso-Large-Precat f) =
    is-iso-inv-iso-Large-Precat
      ( hom-iso-Large-Precat C X Y f)
      ( is-iso-hom-iso-Large-Precat C X Y f)
