# Large precategories

```agda
module category-theory.large-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.functions
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A large precategory is a precategory where we don't fix a universe for the type
of objects or morphisms. (This cannot be done with Σ-types, we must use a record
type.)

## Definition

```agda
record Large-Precat (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor make-Large-Precat
  field
    obj-Large-Precat :
      (l : Level) → UU (α l)
    hom-Large-Precat :
      {l1 l2 : Level} → obj-Large-Precat l1 → obj-Large-Precat l2 →
      Set (β l1 l2)
    compose-hom-Large-Precat :
      {l1 l2 l3 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} →
      type-Set (hom-Large-Precat Y Z) → type-Set (hom-Large-Precat X Y) →
      type-Set (hom-Large-Precat X Z)
    id-hom-Large-Precat :
      {l1 : Level} {X : obj-Large-Precat l1} → type-Set (hom-Large-Precat X X)
    assoc-compose-hom-Large-Precat :
      {l1 l2 l3 l4 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} {W : obj-Large-Precat l4} →
      (h : type-Set (hom-Large-Precat Z W))
      (g : type-Set (hom-Large-Precat Y Z))
      (f : type-Set (hom-Large-Precat X Y)) →
      ( compose-hom-Large-Precat (compose-hom-Large-Precat h g) f) ＝
      ( compose-hom-Large-Precat h (compose-hom-Large-Precat g f))
    left-unit-law-compose-hom-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      ( compose-hom-Large-Precat id-hom-Large-Precat f) ＝ f
    right-unit-law-compose-hom-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      ( compose-hom-Large-Precat f id-hom-Large-Precat) ＝ f

open Large-Precat public

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level}
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  where

  type-hom-Large-Precat : UU (β l1 l2)
  type-hom-Large-Precat = type-Set (hom-Large-Precat C X Y)

  is-set-type-hom-Large-Precat : is-set type-hom-Large-Precat
  is-set-type-hom-Large-Precat = is-set-type-Set (hom-Large-Precat C X Y)

module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 l3 : Level}
  {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2}
  {Z : obj-Large-Precat C l3}
  where

  ap-compose-hom-Large-Precat :
    {g g' : type-hom-Large-Precat C Y Z} (p : g ＝ g')
    {f f' : type-hom-Large-Precat C X Y} (q : f ＝ f') →
    compose-hom-Large-Precat C g f ＝ compose-hom-Large-Precat C g' f'
  ap-compose-hom-Large-Precat p q = ap-binary (compose-hom-Large-Precat C) p q

  compose-hom-Large-Precat' :
    type-hom-Large-Precat C X Y → type-hom-Large-Precat C Y Z →
    type-hom-Large-Precat C X Z
  compose-hom-Large-Precat' f g = compose-hom-Large-Precat C g f
```

## Examples

### The large precategory of sets and functions

The sets and functions, of all universes, form a precategory.

```agda
Set-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
obj-Large-Precat Set-Large-Precat = Set
hom-Large-Precat Set-Large-Precat = hom-Set
compose-hom-Large-Precat Set-Large-Precat g f = g ∘ f
id-hom-Large-Precat Set-Large-Precat = id
assoc-compose-hom-Large-Precat Set-Large-Precat h g f = refl
left-unit-law-compose-hom-Large-Precat Set-Large-Precat f = refl
right-unit-law-compose-hom-Large-Precat Set-Large-Precat f = refl
```
