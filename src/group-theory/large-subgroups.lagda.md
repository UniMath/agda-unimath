# Large subgroups

```agda
module group-theory.large-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.subsets-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.homomorphisms-large-groups
open import group-theory.large-groups
open import group-theory.large-monoids
open import group-theory.large-submonoids
open import group-theory.large-subsemigroups
open import group-theory.subgroups
open import group-theory.subsets-large-groups
```

</details>

## Idea

A {{#concept "subgroup" Disambiguation="of a large group" Agda=Large-Subgroup}}
of a [large group](group-theory.large-subgroups.md) `G` is a
[subset](group-theory.subsets-large-groups.md) `G` that contains the unit and is
closed under multiplication and inverses.

## Definition

```agda
record
  Large-Subgroup
    {α : Level → Level}
    {β : Level → Level → Level}
    (γ : Level → Level)
    (G : Large-Group α β) :
    UUω
  where

  constructor
    make-Large-Subgroup

  field
    large-submonoid-Large-Subgroup :
      Large-Submonoid γ (large-monoid-Large-Group G)

  large-subsemigroup-Large-Subgroup :
    Large-Subsemigroup γ (large-semigroup-Large-Group G)
  large-subsemigroup-Large-Subgroup =
    large-subsemigroup-Large-Submonoid large-submonoid-Large-Subgroup

  subset-Large-Subgroup : subset-Large-Group γ G
  subset-Large-Subgroup =
    subset-Large-Submonoid large-submonoid-Large-Subgroup

  type-Large-Subgroup : (l : Level) → UU (α l ⊔ γ l)
  type-Large-Subgroup =
    type-Large-Submonoid large-submonoid-Large-Subgroup

  inclusion-Large-Subgroup :
    {l : Level} → type-Large-Subgroup l → type-Large-Group G l
  inclusion-Large-Subgroup = pr1

  is-in-Large-Subgroup :
    {l : Level} → type-Large-Group G l → UU (γ l)
  is-in-Large-Subgroup =
    is-in-Large-Submonoid large-submonoid-Large-Subgroup

  prop-is-in-Large-Subgroup :
    {l : Level} → type-Large-Group G l → Prop (γ l)
  prop-is-in-Large-Subgroup =
    prop-is-in-Large-Submonoid large-submonoid-Large-Subgroup

  field
    is-closed-under-inv-Large-Subgroup :
      is-closed-under-inv-subset-Large-Group G subset-Large-Subgroup

  abstract
    eq-type-Large-Subgroup :
      {l : Level} {x y : type-Large-Subgroup l} →
      inclusion-Large-Subgroup x ＝ inclusion-Large-Subgroup y →
      x ＝ y
    eq-type-Large-Subgroup =
      eq-type-Large-Submonoid large-submonoid-Large-Subgroup

  cumulative-large-set-Large-Subgroup :
    Cumulative-Large-Set (λ l → α l ⊔ γ l) β
  cumulative-large-set-Large-Subgroup =
    cumulative-large-set-Subset-Cumulative-Large-Set subset-Large-Subgroup

  contains-unit-Large-Subgroup :
    is-in-Large-Subgroup (unit-Large-Group G)
  contains-unit-Large-Subgroup =
    contains-unit-Large-Submonoid large-submonoid-Large-Subgroup

  contains-raise-unit-Large-Subgroup :
    (l : Level) → is-in-Large-Subgroup (raise-unit-Large-Group G l)
  contains-raise-unit-Large-Subgroup =
    contains-raise-unit-Large-Submonoid large-submonoid-Large-Subgroup

  is-closed-under-mul-subset-Large-Subgroup :
    is-closed-under-mul-subset-Large-Group
      ( G)
      ( subset-Large-Subgroup)
  is-closed-under-mul-subset-Large-Subgroup =
    is-closed-under-mul-subset-Large-Submonoid large-submonoid-Large-Subgroup

open Large-Subgroup public
```

## Properties

### Large subgroups induce large groups

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Group α β}
  (S : Large-Subgroup γ G)
  where

  large-monoid-Large-Subgroup :
    Large-Monoid (λ l → α l ⊔ γ l) β
  large-monoid-Large-Subgroup =
    large-monoid-Large-Submonoid (large-submonoid-Large-Subgroup S)

  mul-Large-Subgroup :
    {l1 l2 : Level} →
    type-Large-Subgroup S l1 → type-Large-Subgroup S l2 →
    type-Large-Subgroup S (l1 ⊔ l2)
  mul-Large-Subgroup = mul-Large-Monoid large-monoid-Large-Subgroup

  inv-Large-Subgroup :
    {l : Level} → type-Large-Subgroup S l → type-Large-Subgroup S l
  inv-Large-Subgroup (x , x∈S) =
    ( inv-Large-Group G x , is-closed-under-inv-Large-Subgroup S x x∈S)

  unit-Large-Subgroup : type-Large-Subgroup S lzero
  unit-Large-Subgroup = unit-Large-Monoid large-monoid-Large-Subgroup

  raise-unit-Large-Subgroup : (l : Level) → type-Large-Subgroup S l
  raise-unit-Large-Subgroup =
    raise-unit-Large-Monoid large-monoid-Large-Subgroup

  abstract
    preserves-sim-inv-Large-Subgroup :
      preserves-sim-endomap-Cumulative-Large-Set
        ( id)
        ( cumulative-large-set-Large-Subgroup S)
        ( inv-Large-Subgroup)
    preserves-sim-inv-Large-Subgroup (x , _) (y , _) =
      preserves-sim-inv-Large-Group G x y

    left-inverse-law-mul-Large-Subgroup :
      {l : Level} (x : type-Large-Subgroup S l) →
      mul-Large-Subgroup (inv-Large-Subgroup x) x ＝ raise-unit-Large-Subgroup l
    left-inverse-law-mul-Large-Subgroup (x , _) =
      eq-type-Large-Subgroup
        ( S)
        ( left-inverse-law-mul-Large-Group G x)

    right-inverse-law-mul-Large-Subgroup :
      {l : Level} (x : type-Large-Subgroup S l) →
      mul-Large-Subgroup x (inv-Large-Subgroup x) ＝ raise-unit-Large-Subgroup l
    right-inverse-law-mul-Large-Subgroup (x , _) =
      eq-type-Large-Subgroup
        ( S)
        ( right-inverse-law-mul-Large-Group G x)

  large-group-Large-Subgroup : Large-Group (λ l → α l ⊔ γ l) β
  large-group-Large-Subgroup =
    make-Large-Group
      ( large-monoid-Large-Subgroup)
      ( inv-Large-Subgroup)
      ( preserves-sim-inv-Large-Subgroup)
      ( left-inverse-law-mul-Large-Subgroup)
      ( right-inverse-law-mul-Large-Subgroup)
```

### The inclusion homomorphism of large subgroups

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Group α β}
  (S : Large-Subgroup γ G)
  where

  inclusion-hom-Large-Subgroup :
    hom-Large-Group
      ( large-group-Large-Subgroup S)
      ( G)
  inclusion-hom-Large-Subgroup =
    make-hom-Large-Group
      ( inclusion-hom-Large-Subsemigroup
        ( large-subsemigroup-Large-Subgroup S))
```

### Small subgroups from large subgroups

```agda
module _
  {α γ : Level → Level}
  {β : Level → Level → Level}
  {G : Large-Group α β}
  (S : Large-Subgroup γ G)
  where

  subgroup-Large-Subgroup : (l : Level) → Subgroup (γ l) (group-Large-Group G l)
  subgroup-Large-Subgroup l =
    ( prop-is-in-Large-Subgroup S ,
      contains-raise-unit-Large-Subgroup S l ,
      is-closed-under-mul-subset-Large-Subgroup S _ _ ,
      is-closed-under-inv-Large-Subgroup S _)
```
