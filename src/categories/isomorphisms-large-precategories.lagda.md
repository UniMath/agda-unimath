# Isomorphisms in large precategories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.isomorphisms-large-precategories where

open import categories.large-precategories using
  ( Large-Precat; obj-Large-Precat; type-hom-Large-Precat;
    comp-Large-Precat; id-Large-Precat;
    right-unit-law-comp-Large-Precat;
    associative-comp-Large-Precat; comp-Large-Precat';
    left-unit-law-comp-Large-Precat; hom-Large-Precat;
    is-set-type-hom-Large-Precat)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap)
open import foundation.propositions using
  ( prod-Prop; is-prop; is-prop-all-elements-equal)
open import foundation.sets using (Id-Prop; is-set; UU-Set)
open import foundation.subtypes using (eq-subtype; is-set-is-subtype)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

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
      ( Id (comp-Large-Precat C f g) (id-Large-Precat C)) ×
      ( Id (comp-Large-Precat C g f) (id-Large-Precat C)))

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
    Id ( comp-Large-Precat C (hom-iso-Large-Precat f) (hom-inv-iso-Large-Precat f))
       ( id-Large-Precat C)
  is-sec-hom-inv-iso-Large-Precat f = pr1 (pr2 (pr2 f))

  is-retr-hom-inv-iso-Large-Precat :
    (f : iso-Large-Precat) →
    Id ( comp-Large-Precat C (hom-inv-iso-Large-Precat f) (hom-iso-Large-Precat f))
       ( id-Large-Precat C)
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
  pr1 id-iso-Large-Precat = id-Large-Precat C
  pr1 (pr2 id-iso-Large-Precat) = id-Large-Precat C
  pr1 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-Large-Precat C (id-Large-Precat C)
  pr2 (pr2 (pr2 id-iso-Large-Precat)) =
    left-unit-law-comp-Large-Precat C (id-Large-Precat C)
```

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them. This is because by the J-rule, it is enough to construct an isomorphism given `refl : Id x x`, from `x` to itself. We take the identity morphism as such an isomorphism.

```agda
iso-eq-Large-Precat :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Large-Precat α β) {l1 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l1) →
  Id X Y → iso-Large-Precat C X Y
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
    (H K : is-iso-Large-Precat C f) → Id H K
  all-elements-equal-is-iso-Large-Precat f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-subtype
      ( λ g →
        prod-Prop
          ( Id-Prop
            ( hom-Large-Precat C Y Y)
            ( comp-Large-Precat C f g)
            ( id-Large-Precat C))
          ( Id-Prop
            ( hom-Large-Precat C X X)
            ( comp-Large-Precat C g f)
            ( id-Large-Precat C)))
      ( ( inv (right-unit-law-comp-Large-Precat C g)) ∙
        ( ( ap ( comp-Large-Precat C g) (inv p')) ∙
          ( ( inv (associative-comp-Large-Precat C g f g')) ∙
            ( ( ap ( comp-Large-Precat' C g') q) ∙
              ( left-unit-law-comp-Large-Precat C g')))))

  is-prop-is-iso-Large-Precat :
    (f : type-hom-Large-Precat C X Y) → is-prop (is-iso-Large-Precat C f)
  is-prop-is-iso-Large-Precat f =
    is-prop-all-elements-equal (all-elements-equal-is-iso-Large-Precat f)
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
    is-set-is-subtype
      ( is-prop-is-iso-Large-Precat C X Y)
      ( is-set-type-hom-Large-Precat C X Y)

  iso-Large-Precat-Set : UU-Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Large-Precat-Set = iso-Large-Precat C X Y
  pr2 iso-Large-Precat-Set = is-set-iso-Large-Precat
```
