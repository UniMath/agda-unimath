# The universal property of family of fibers of maps

```agda
module foundation-core.universal-property-family-of-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.extensions-families-of-elements
open import foundation.function-extensionality
open import foundation.lifts-families-of-elements
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

Any map `f : A → B` induces a type family `fiber f : B → 𝒰` of
[fibers](foundation-core.fibers-of-maps.md) of `f`. By
[precomposing](foundation.precomposition-type-families.md) with `f`, we obtain
the type family `(fiber f) ∘ f : A → 𝒰`, which always has a section given by

```text
  λ a → (a , refl) : (a : A) → fiber f (f a).
```

We can uniquely characterize the family of fibers `fiber f : B → 𝒰` as the
initial type family equipped with such a section. Explicitly, the
{{#concept "universal property of the family of fibers" Disambiguation="of a map"}}
`fiber f : B → 𝒰` of a map `f` is that the precomposition operation

```text
  ((b : B) → fiber f b → P b) → ((a : A) → P (f a))
```

is an [equivalence](foundation-core.equivalences.md) for any type family
`P : B → 𝒰`. Note that for any type family `P` over `B` and any map `f : A → B`,
the type of [lifts](foundation.lifts-of-families-of-elements.md) of `f` to `P`
is precisely the type of sections

```text
  (a : A) → P (f a).
```

The family of fibers of `f` is therefore the initial type family over `B`
equipped with a lift of `f`.

This universal property is especially useful when `A` or `B` enjoy mapping out
universal properties. This lets us characterize the sections `(a : A) → P (f a)`
in terms of the mapping out properties of `A` and the descent data of `B`.

**Note:** We disambiguate between the _universal property of the family of
fibers of a map_ and the _universal property of the fiber of a map_ at a point
in the codomain. The universal property of the family of fibers of a map is as
described above, while the universal property of the fiber `fiber f b` of a map
`f` at `b` is a special case of the universal property of pullbacks.

## Definitions

### The canonical map used in the universal property and dependent universal property of the family of fibers of a map

The underlying map of the universal property of the family of fibers of a map is
defined to be the evaluation map

```text
  ((b : B) (z : F b) → P b z) → ((a : A) → P (f a) (δ a))
```

for any type family `F : B → 𝒰` equipped with a lift `δ : (a : A) → F (f a)`.
This map takes a dependent function `h` and evaluates it at the values of the
lift `δ`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (F : B → UU l3) (δ : lift-family-of-elements f F)
  where

  ev-lift-family-of-elements' :
    {l4 : Level} {P : (b : B) → F b → UU l4} →
    ((b : B) (z : F b) → P b z) → dependent-lift-family-of-elements δ (P ∘ f)
  ev-lift-family-of-elements' h a = h (f a) (δ a)
```

### The universal property of the fibers of a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  universal-property-family-of-fibers :
    (f : A → B) (F : B → UU l3) (δ : lift-family-of-elements f F) → UUω
  universal-property-family-of-fibers f F δ =
    {l : Level} (P : B → UU l) →
    is-equiv (ev-lift-family-of-elements' f F δ {l} {λ b _ → P b})
```

### The dependent universal property of the fibers of a map

```agda
  dependent-universal-property-family-of-fibers :
    (f : A → B) (F : B → UU l3) (δ : lift-family-of-elements f F) → UUω
  dependent-universal-property-family-of-fibers f F δ =
    {l : Level} (P : (b : B) → F b → UU l) →
    is-equiv (ev-lift-family-of-elements' f F δ {l} {P})
```

### The lift of any map to its family of fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  lift-family-of-elements-fiber : lift-family-of-elements f (fiber f)
  pr1 (lift-family-of-elements-fiber a) = a
  pr2 (lift-family-of-elements-fiber a) = refl
```

## Properties

### The family of fibers of a map satisfies the dependent universal property of the family of fibers of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  module _
    {l3 : Level} (C : (y : B) (z : fiber f y) → UU l3)
    where

    ev-lift-family-of-elements-fiber :
      ((y : B) (z : fiber f y) → C y z) → ((x : A) → C (f x) (x , refl))
    ev-lift-family-of-elements-fiber =
      ev-lift-family-of-elements' f (fiber f) (lift-family-of-elements-fiber f)

    extend-lift-family-of-elements-fiber :
      ((x : A) → C (f x) (x , refl)) → ((y : B) (z : fiber f y) → C y z)
    extend-lift-family-of-elements-fiber h .(f x) (x , refl) = h x

    is-section-extend-lift-family-of-elements-fiber :
      is-section
        ( ev-lift-family-of-elements-fiber)
        ( extend-lift-family-of-elements-fiber)
    is-section-extend-lift-family-of-elements-fiber h = refl

    is-retraction-extend-lift-family-of-elements-fiber' :
      (h : (y : B) (z : fiber f y) → C y z) (y : B) →
      extend-lift-family-of-elements-fiber
        ( ev-lift-family-of-elements-fiber h)
        ( y) ~
      h y
    is-retraction-extend-lift-family-of-elements-fiber' h .(f z) (z , refl) =
      refl

    is-retraction-extend-lift-family-of-elements-fiber :
      is-retraction
        ( ev-lift-family-of-elements-fiber)
        ( extend-lift-family-of-elements-fiber)
    is-retraction-extend-lift-family-of-elements-fiber h =
      eq-htpy (eq-htpy ∘ is-retraction-extend-lift-family-of-elements-fiber' h)

    is-equiv-extend-lift-family-of-elements-fiber :
      is-equiv extend-lift-family-of-elements-fiber
    is-equiv-extend-lift-family-of-elements-fiber =
      is-equiv-is-invertible
        ( ev-lift-family-of-elements-fiber)
        ( is-retraction-extend-lift-family-of-elements-fiber)
        ( is-section-extend-lift-family-of-elements-fiber)

    inv-equiv-dependent-universal-property-family-of-fibers :
      ((x : A) → C (f x) (x , refl)) ≃ ((y : B) (z : fiber f y) → C y z)
    pr1 inv-equiv-dependent-universal-property-family-of-fibers =
      extend-lift-family-of-elements-fiber
    pr2 inv-equiv-dependent-universal-property-family-of-fibers =
      is-equiv-extend-lift-family-of-elements-fiber

  dependent-universal-property-family-of-fibers-fiber :
    dependent-universal-property-family-of-fibers f
      ( fiber f)
      ( lift-family-of-elements-fiber f)
  dependent-universal-property-family-of-fibers-fiber C =
    is-equiv-is-invertible
      ( extend-lift-family-of-elements-fiber C)
      ( is-section-extend-lift-family-of-elements-fiber C)
      ( is-retraction-extend-lift-family-of-elements-fiber C)

  equiv-dependent-universal-property-family-of-fibers :
    {l3 : Level} (C : (y : B) (z : fiber f y) → UU l3) →
    ((y : B) (z : fiber f y) → C y z) ≃
    ((x : A) → C (f x) (x , refl))
  pr1 (equiv-dependent-universal-property-family-of-fibers C) =
    ev-lift-family-of-elements-fiber C
  pr2 (equiv-dependent-universal-property-family-of-fibers C) =
    dependent-universal-property-family-of-fibers-fiber C
```

### The family of fibers of a map satisfies the dependent universal property of the family of fibers of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  universal-property-family-of-fibers-fiber :
    universal-property-family-of-fibers f
      ( fiber f)
      ( lift-family-of-elements-fiber f)
  universal-property-family-of-fibers-fiber C =
    dependent-universal-property-family-of-fibers-fiber f (λ y _ → C y)

  equiv-universal-property-family-of-fibers :
    {l3 : Level} (C : B → UU l3) →
    ((y : B) → fiber f y → C y) ≃ lift-family-of-elements f C
  equiv-universal-property-family-of-fibers C =
    equiv-dependent-universal-property-family-of-fibers f (λ y _ → C y)
```

### The inverse equivalence of the universal property of the family of fibers of a map

The inverse of the equivalence `equiv-universal-property-family-of-fibers` has a
reasonably nice definition, so we also record it here.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  inv-equiv-universal-property-family-of-fibers :
    (lift-family-of-elements f C) ≃ ((y : B) → fiber f y → C y)
  inv-equiv-universal-property-family-of-fibers =
    inv-equiv-dependent-universal-property-family-of-fibers f (λ y _ → C y)
```

### A type family `C` over `B` satisfies the universal property of the family of fibers of a map `f : A → B` if and only if the diagonal map `C b → (fiber f b → C b)` is an equivalence for every `b : B`

This condition simplifies, for example, the proof that connected maps satisfy a
dependent universal property.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-precomp-Π-fiber-condition :
    {l3 : Level} {C : B → UU l3} →
    ((b : B) → is-equiv (λ (c : C b) → const (fiber f b) (C b) c)) →
    is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-fiber-condition {l3} {C} H =
    is-equiv-comp
      ( ev-lift-family-of-elements-fiber f (λ b _ → C b))
      ( map-Π (λ b u _ → u))
      ( is-equiv-map-Π-is-fiberwise-equiv H)
      ( universal-property-family-of-fibers-fiber f C)
```
