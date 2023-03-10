# Functors between large precategories

```agda
module category-theory.functors-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import Agda.Primitive using (Setω)

open import category-theory.large-precategories

open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A functor from a large precategory `C` to a large precategory `D` consists of:
- a map `F : C → D` on objects,
- a map `Fmap : hom x y → hom (F x) (F y)` on morphisms,
such that the following identities hold:
- `Fmap id_x = id_(F x)`,
- `Fmap (comp g f) = comp (F g) (F f)`.

## Definition

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  where

  record functor-Large-Precat (γ : Level → Level) : Setω
    where
    constructor make-functor
    field
      obj-functor-Large-Precat :
        {l1 : Level} → obj-Large-Precat C l1 → obj-Large-Precat D (γ l1)
      hom-functor-Large-Precat :
        {l1 l2 : Level}
        {X : obj-Large-Precat C l1} {Y : obj-Large-Precat C l2} →
        type-hom-Large-Precat C X Y →
        type-hom-Large-Precat D
          ( obj-functor-Large-Precat X)
          ( obj-functor-Large-Precat Y)
      preserves-comp-functor-Large-Precat :
        {l1 l2 l3 : Level} {X : obj-Large-Precat C l1}
        {Y : obj-Large-Precat C l2} {Z : obj-Large-Precat C l3}
        (g : type-hom-Large-Precat C Y Z) (f : type-hom-Large-Precat C X Y) →
        ( hom-functor-Large-Precat (comp-hom-Large-Precat C g f)) ＝
        ( comp-hom-Large-Precat D
          ( hom-functor-Large-Precat g)
          ( hom-functor-Large-Precat f))
      preserves-id-functor-Large-Precat :
        {l1 : Level} {X : obj-Large-Precat C l1} →
        ( hom-functor-Large-Precat (id-hom-Large-Precat C {X = X})) ＝
        ( id-hom-Large-Precat D {X = obj-functor-Large-Precat X})

  open functor-Large-Precat public
```

## Examples

### The identity functor

There is an identity functor on any large precategory.

```agda
id-functor-Large-Precat :
  {αC : Level → Level} {βC : Level → Level → Level} →
  {C : Large-Precat αC βC} →
  functor-Large-Precat C C (λ l → l)
obj-functor-Large-Precat id-functor-Large-Precat = id
hom-functor-Large-Precat id-functor-Large-Precat = id
preserves-comp-functor-Large-Precat id-functor-Large-Precat g f = refl
preserves-id-functor-Large-Precat id-functor-Large-Precat = refl
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Large-Precat :
  {αC αD αE γG γF : Level → Level} {βC βD βE : Level → Level → Level} →
  {C : Large-Precat αC βC} {D : Large-Precat αD βD} {E : Large-Precat αE βE} →
  functor-Large-Precat D E γG → functor-Large-Precat C D γF →
  functor-Large-Precat C E (λ l → γG (γF l))
obj-functor-Large-Precat (comp-functor-Large-Precat G F) =
  obj-functor-Large-Precat G ∘ obj-functor-Large-Precat F
hom-functor-Large-Precat (comp-functor-Large-Precat G F) =
  hom-functor-Large-Precat G ∘ hom-functor-Large-Precat F
preserves-comp-functor-Large-Precat (comp-functor-Large-Precat G F) g f =
  ( ap
    ( hom-functor-Large-Precat G)
    ( preserves-comp-functor-Large-Precat F g f)) ∙
  ( preserves-comp-functor-Large-Precat G
    ( hom-functor-Large-Precat F g)
    ( hom-functor-Large-Precat F f))
preserves-id-functor-Large-Precat (comp-functor-Large-Precat G F) =
  ( ap ( hom-functor-Large-Precat G)
       ( preserves-id-functor-Large-Precat F)) ∙
  ( preserves-id-functor-Large-Precat G)
```
