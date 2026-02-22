# Dependent products of large groups

```agda
module group-theory.dependent-products-large-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.function-types
open import foundation.large-binary-relations
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-large-similarity-relations
open import foundation.universe-levels

open import group-theory.dependent-products-large-monoids
open import group-theory.large-groups
open import group-theory.large-monoids
```

</details>

## Idea

The dependent product of a family of
[large groups](group-theory.large-groups.md) is a large group.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (A : UU l0)
  (G : A → Large-Group α β)
  where

  large-monoid-Π-Large-Group :
    Large-Monoid (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  large-monoid-Π-Large-Group =
    Π-Large-Monoid A (λ a → large-monoid-Large-Group (G a))

  cumulative-large-set-Π-Large-Group :
    Cumulative-Large-Set (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  cumulative-large-set-Π-Large-Group =
    cumulative-large-set-Large-Monoid large-monoid-Π-Large-Group

  type-Π-Large-Group : (l : Level) → UU (l0 ⊔ α l)
  type-Π-Large-Group l = (a : A) → type-Large-Group (G a) l

  mul-Π-Large-Group :
    {l1 l2 : Level} →
    type-Π-Large-Group l1 → type-Π-Large-Group l2 → type-Π-Large-Group (l1 ⊔ l2)
  mul-Π-Large-Group = mul-Large-Monoid large-monoid-Π-Large-Group

  unit-Π-Large-Group : type-Π-Large-Group lzero
  unit-Π-Large-Group = unit-Large-Monoid large-monoid-Π-Large-Group

  sim-Π-Large-Group :
    Large-Relation (λ l1 l2 → l0 ⊔ β l1 l2) type-Π-Large-Group
  sim-Π-Large-Group = sim-Large-Monoid large-monoid-Π-Large-Group

  inv-Π-Large-Group :
    {l : Level} → type-Π-Large-Group l → type-Π-Large-Group l
  inv-Π-Large-Group g a = inv-Large-Group (G a) (g a)

  sim-left-inverse-law-mul-Π-Large-Group :
    {l : Level} (f : type-Π-Large-Group l) →
    sim-Π-Large-Group
      ( mul-Π-Large-Group (inv-Π-Large-Group f) f)
      ( unit-Π-Large-Group)
  sim-left-inverse-law-mul-Π-Large-Group f a =
    sim-left-inverse-law-mul-Large-Group (G a) (f a)

  sim-right-inverse-law-mul-Π-Large-Group :
    {l : Level} (f : type-Π-Large-Group l) →
    sim-Π-Large-Group
      ( mul-Π-Large-Group f (inv-Π-Large-Group f))
      ( unit-Π-Large-Group)
  sim-right-inverse-law-mul-Π-Large-Group f a =
    sim-right-inverse-law-mul-Large-Group (G a) (f a)

  Π-Large-Group : Large-Group (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  Π-Large-Group =
    λ where
      .large-monoid-Large-Group →
        large-monoid-Π-Large-Group
      .inv-Large-Group →
        inv-Π-Large-Group
      .sim-left-inverse-law-mul-Large-Group →
        sim-left-inverse-law-mul-Π-Large-Group
      .sim-right-inverse-law-mul-Large-Group →
        sim-right-inverse-law-mul-Π-Large-Group
```
