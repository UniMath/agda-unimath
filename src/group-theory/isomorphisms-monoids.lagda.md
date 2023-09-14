# Isomorphisms of monoids

```agda
module group-theory.isomorphisms-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.precategory-of-monoids
```

</details>

## Idea

An **isomorphism** of [monoids](group-theory.monoids.md) is an invertible [homomorphism of monoids](group-theory.homomorphisms-monoids.md).

## Definitions

### The predicate of being an isomorphism

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : type-hom-Monoid M N)
  where

  is-iso-hom-Monoid : UU (l1 ⊔ l2)
  is-iso-hom-Monoid =
    is-iso-hom-Large-Precategory Monoid-Large-Precategory {X = M} {Y = N} f

  hom-inv-is-iso-hom-Monoid :
    is-iso-hom-Monoid → type-hom-Monoid N M
  hom-inv-is-iso-hom-Monoid =
    hom-inv-is-iso-hom-Large-Precategory Monoid-Large-Precategory f

  is-section-hom-inv-is-iso-hom-Monoid :
    (H : is-iso-hom-Monoid) →
    comp-hom-Monoid f (hom-inv-is-iso-hom-Monoid H) ＝
    id-hom-Monoid
  is-section-hom-inv-is-iso-hom-Monoid =
    is-section-hom-inv-is-iso-hom-Large-Precategory Monoid-Large-Precategory f

  is-retraction-hom-inv-is-iso-hom-Monoid :
    (H : is-iso-hom-Monoid) →
    comp-hom-Monoid (hom-inv-is-iso-hom-Monoid H) f ＝
    id-hom-Monoid
  is-retraction-hom-inv-is-iso-hom-Monoid =
    is-retraction-hom-inv-is-iso-hom-Large-Precategory Monoid-Large-Precategory f
```

### Isomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  iso-Monoid : UU ?
  iso-Monoid =
    iso-Large-Precategory Monoid-Large-Precategory M N

  hom-iso-Monoid :
    iso-Monoid → type-hom-Monoid M N
  hom-iso-Monoid =
    hom-iso-Large-Precategory Monoid-Large-Precategory M N

  is-iso-iso-Monoid :
    (f : iso-Monoid) →
    is-iso-hom-Monoid (hom-iso-Monoid f)
  is-iso-iso-Monoid =
    is-iso-iso-Large-Precategory Monoid-Large-Precategory M N

  hom-inv-iso-Monoid :
    iso-Monoid → type-hom-Monoid N M
  hom-inv-iso-Monoid =
    hom-inv-iso-Large-Precategory Monoid-Large-Precategory M N

  is-section-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    ( comp-hom-Monoid
      ( hom-iso-Monoid f)
      ( hom-inv-iso-Monoid f)) ＝
    ( id-hom-Monoid)
  is-section-hom-inv-iso-Monoid =
    is-section-hom-inv-iso-Large-Precategory Monoid-Large-Precategory M N

  is-retraction-hom-inv-iso-Monoid :
    (f : iso-Monoid) →
    ( comp-hom-Monoid
      ( hom-inv-iso-Monoid f)
      ( hom-iso-Monoid f)) ＝
    ( id-hom-Monoid)
  is-retraction-hom-inv-iso-Monoid =
    is-retraction-hom-inv-iso-Large-Precategory Monoid-Large-Precategory M N
```

## Examples

### The identity morphisms are isomorphisms

For any object `x : A`, the identity morphism `id_x : hom x x` is an isomorphism
from `x` to `x` since `id_x ∘ id_x = id_x` (it is its own inverse).

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Monoid α β) {l1 : Level} {M : obj-Monoid l1}
  where

  is-iso-id-hom-Monoid :
    is-iso-hom-Monoid (id-hom-Monoid {M = M})
  pr1 is-iso-id-hom-Monoid = id-hom-Monoid
  pr1 (pr2 is-iso-id-hom-Monoid) =
    left-unit-law-comp-hom-Monoid (id-hom-Monoid)
  pr2 (pr2 is-iso-id-hom-Monoid) =
    left-unit-law-comp-hom-Monoid (id-hom-Monoid)

  id-iso-Monoid : iso-Monoid M M
  pr1 id-iso-Monoid = id-hom-Monoid
  pr2 id-iso-Monoid = is-iso-id-hom-Monoid
```

### Equalities give rise to isomorphisms

An equality between objects `x y : A` gives rise to an isomorphism between them.
This is because by the J-rule, it is enough to construct an isomorphism given
`refl : Id x x`, from `x` to itself. We take the identity morphism as such an
isomorphism.

```agda
iso-eq-Monoid :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Monoid α β) {l1 : Level}
  (M : obj-Monoid l1) (N : obj-Monoid l1) →
  M ＝ N → iso-Monoid M N
iso-eq-Monoid M .M refl = id-iso-Monoid

compute-iso-eq-Monoid :
  {α : Level → Level} {β : Level → Level → Level} →
  (C : Monoid α β) {l1 : Level}
  (M : obj-Monoid l1) (N : obj-Monoid l1) →
  iso-eq-Precategory (precategory-Monoid l1) M N ~
  iso-eq-Monoid M N
compute-iso-eq-Monoid M .M refl = refl
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
  (C : Monoid α β) {l1 l2 : Level}
  (M : obj-Monoid l1) (N : obj-Monoid l2)
  where

  all-elements-equal-is-iso-hom-Monoid :
    (f : type-hom-Monoid M N)
    (H K : is-iso-hom-Monoid f) → H ＝ K
  all-elements-equal-is-iso-hom-Monoid f
    (pair g (pair p q)) (pair g' (pair p' q')) =
    eq-type-subtype
      ( λ g →
        prod-Prop
          ( Id-Prop
            ( hom-Monoid N N)
            ( comp-hom-Monoid f g)
            ( id-hom-Monoid))
          ( Id-Prop
            ( hom-Monoid M M)
            ( comp-hom-Monoid g f)
            ( id-hom-Monoid)))
      ( ( inv (right-unit-law-comp-hom-Monoid g)) ∙
        ( ( ap ( comp-hom-Monoid g) (inv p')) ∙
          ( ( inv (associative-comp-hom-Monoid g f g')) ∙
            ( ( ap ( comp-hom-Monoid' g') q) ∙
              ( left-unit-law-comp-hom-Monoid g')))))

  is-prop-is-iso-hom-Monoid :
    (f : type-hom-Monoid M N) →
    is-prop (is-iso-hom-Monoid f)
  is-prop-is-iso-hom-Monoid f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-iso-hom-Monoid f)

  is-iso-prop-hom-Monoid :
    (f : type-hom-Monoid M N) → Prop ?
  pr1 (is-iso-prop-hom-Monoid f) =
    is-iso-hom-Monoid f
  pr2 (is-iso-prop-hom-Monoid f) =
    is-prop-is-iso-hom-Monoid f
```

### The type of isomorphisms form a set

The type of isomorphisms between objects `x y : A` is a subtype of the set
`hom x y` since being an isomorphism is a proposition.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Monoid α β) {l1 l2 : Level}
  (M : obj-Monoid l1) (N : obj-Monoid l2)
  where

  is-set-iso-Monoid : is-set (iso-Monoid M N)
  is-set-iso-Monoid =
    is-set-type-subtype
      ( is-iso-prop-hom-Monoid M N)
      ( is-set-type-hom-Monoid M N)

  iso-Monoid-Set : Set (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
  pr1 iso-Monoid-Set = iso-Monoid M N
  pr2 iso-Monoid-Set = is-set-iso-Monoid
```

### Isomorphisms are stable by composition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Monoid α β) {l1 l2 l3 : Level}
  (M : obj-Monoid l1) (N : obj-Monoid l2)
  (Z : obj-Monoid l3)
  where

  is-iso-comp-iso-Monoid :
    (g : type-hom-Monoid N Z) →
    (f : type-hom-Monoid M N) →
    is-iso-hom-Monoid g → is-iso-hom-Monoid f →
    is-iso-hom-Monoid (comp-hom-Monoid g f)
  pr1 (is-iso-comp-iso-Monoid g f q p) =
    comp-hom-Monoid
      ( hom-inv-iso-Monoid M N (pair f p))
      ( hom-inv-iso-Monoid N Z (pair g q))
  pr1 (pr2 (is-iso-comp-iso-Monoid g f q p)) =
    ( associative-comp-hom-Monoid g f
      ( pr1 (is-iso-comp-iso-Monoid g f q p))) ∙
      ( ( ap
        ( comp-hom-Monoid g)
        ( ( inv
          ( associative-comp-hom-Monoid f
            ( hom-inv-iso-Monoid M N (pair f p))
            ( hom-inv-iso-Monoid N Z (pair g q)))) ∙
          ( ( ap
            ( λ h →
              comp-hom-Monoid h
                (hom-inv-iso-Monoid N Z (pair g q)))
            ( is-section-hom-inv-iso-Monoid M N (pair f p))) ∙
            ( left-unit-law-comp-hom-Monoid
              ( hom-inv-iso-Monoid N Z (pair g q)))))) ∙
        ( is-section-hom-inv-iso-Monoid N Z (pair g q)))
  pr2 (pr2 (is-iso-comp-iso-Monoid g f q p)) =
    ( associative-comp-hom-Monoid
      ( hom-inv-iso-Monoid M N (pair f p))
      ( hom-inv-iso-Monoid N Z (pair g q))
      ( comp-hom-Monoid g f)) ∙
      ( ( ap
        ( comp-hom-Monoid
          ()
          ( hom-inv-iso-Monoid M N (pair f p)))
        ( ( inv
          ( associative-comp-hom-Monoid
            ( hom-inv-iso-Monoid N Z (pair g q))
            ( g)
            ( f))) ∙
          ( ( ap
            ( λ h → comp-hom-Monoid h f)
            ( is-retraction-hom-inv-iso-Monoid N Z (pair g q))) ∙
            ( left-unit-law-comp-hom-Monoid f)))) ∙
        ( is-retraction-hom-inv-iso-Monoid M N (pair f p)))

  comp-iso-Monoid :
    iso-Monoid N Z →
    iso-Monoid M N →
    iso-Monoid M Z
  pr1 (comp-iso-Monoid g f) =
    comp-hom-Monoid
      ( hom-iso-Monoid N Z g)
      ( hom-iso-Monoid M N f)
  pr2 (comp-iso-Monoid f g) =
    is-iso-comp-iso-Monoid
      ( hom-iso-Monoid N Z f)
      ( hom-iso-Monoid M N g)
      ( is-iso-iso-Monoid N Z f)
      ( is-iso-iso-Monoid M N g)
```

### Isomorphisms are stable by inversion

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Monoid α β) {l1 l2 : Level}
  (M : obj-Monoid l1) (N : obj-Monoid l2)
  where

  is-iso-inv-iso-Monoid :
    (f : type-hom-Monoid M N) →
    (p : is-iso-hom-Monoid f) →
    is-iso-hom-Monoid (hom-inv-iso-Monoid M N (f , p))
  pr1 (is-iso-inv-iso-Monoid f p) = f
  pr1 (pr2 (is-iso-inv-iso-Monoid f p)) =
    is-retraction-hom-inv-iso-Monoid M N (pair f p)
  pr2 (pr2 (is-iso-inv-iso-Monoid f p)) =
    is-section-hom-inv-iso-Monoid M N (pair f p)

  inv-iso-Monoid :
    iso-Monoid M N →
    iso-Monoid N M
  pr1 (inv-iso-Monoid f) = hom-inv-iso-Monoid M N f
  pr2 (inv-iso-Monoid f) =
    is-iso-inv-iso-Monoid
      ( hom-iso-Monoid M N f)
      ( is-iso-iso-Monoid M N f)
```
