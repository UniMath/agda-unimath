# Large precategories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.large-precategories where

open import Agda.Primitive using (Setω)
open import foundation.functions using (_∘_; id)
open import foundation.identity-types using (Id; refl)
open import foundation.sets using (UU-Set; type-Set; hom-Set)
open import foundation.universe-levels using (UU; Level; lsuc; _⊔_)
```

## Idea

A large precategory is a precategory where we don't fix a universe for the type of objects or morphisms. (This cannot be done with Σ-types, we must use a record type.)

```agda
record Large-Precat (α : Level → Level) (β : Level → Level → Level) : Setω where
  constructor make-Large-Precat
  field
    obj-Large-Precat :
      (l : Level) → UU (α l)
    hom-Large-Precat :
      {l1 l2 : Level} → obj-Large-Precat l1 → obj-Large-Precat l2 →
      UU-Set (β l1 l2)
    comp-Large-Precat :
      {l1 l2 l3 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} →
      type-Set (hom-Large-Precat Y Z) → type-Set (hom-Large-Precat X Y) →
      type-Set (hom-Large-Precat X Z)
    id-Large-Precat :
      {l1 : Level} {X : obj-Large-Precat l1} → type-Set (hom-Large-Precat X X)
    associative-comp-Large-Precat :
      {l1 l2 l3 l4 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      {Z : obj-Large-Precat l3} {W : obj-Large-Precat l4} →
      (h : type-Set (hom-Large-Precat Z W))
      (g : type-Set (hom-Large-Precat Y Z))
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-Large-Precat (comp-Large-Precat h g) f)
         ( comp-Large-Precat h (comp-Large-Precat g f))
    left-unit-law-comp-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-Large-Precat id-Large-Precat f) f
    right-unit-law-comp-Large-Precat :
      {l1 l2 : Level} {X : obj-Large-Precat l1} {Y : obj-Large-Precat l2}
      (f : type-Set (hom-Large-Precat X Y)) →
      Id ( comp-Large-Precat f id-Large-Precat) f

open Large-Precat public
```

## Examples

### The large precategory of sets and functions

The sets and functions, of all universes, form a precategory.

```agda
Set-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
obj-Large-Precat Set-Large-Precat = UU-Set
hom-Large-Precat Set-Large-Precat = hom-Set
comp-Large-Precat Set-Large-Precat g f = g ∘ f
id-Large-Precat Set-Large-Precat = id
associative-comp-Large-Precat Set-Large-Precat h g f = refl
left-unit-law-comp-Large-Precat Set-Large-Precat f = refl
right-unit-law-comp-Large-Precat Set-Large-Precat f = refl
```
