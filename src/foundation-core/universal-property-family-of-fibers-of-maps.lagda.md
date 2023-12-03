# The universal property of family of fibers of maps

```agda
module foundation-core.universal-property-family-of-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
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
the type of _lifts_ of `f` to `P` is precisely the type of sections

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
lift `δ`. Hence we call it `ev-lift`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (F : B → UU l3) (δ : (a : A) → F (f a))
  where

  ev-lift :
    {l4 : Level} {P : (b : B) → F b → UU l4} →
    ((b : B) (z : F b) → P b z) → (a : A) → P (f a) (δ a)
  ev-lift h a = h (f a) (δ a)
```

### The universal property of the fibers of a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  universal-property-family-of-fibers :
    (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) → UUω
  universal-property-family-of-fibers f F δ =
    {l : Level} (P : B → UU l) → is-equiv (ev-lift f F δ {l} {λ b _ → P b})
```

### The dependent universal property of the fibers of a map

```agda
  dependent-universal-property-family-of-fibers :
    (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) → UUω
  dependent-universal-property-family-of-fibers f F δ =
    {l : Level} (P : (b : B) → F b → UU l) → is-equiv (ev-lift f F δ {l} {P})
```

### The lift of any map to its family of fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  lift-family-of-fibers : (a : A) → fiber f (f a)
  pr1 (lift-family-of-fibers a) = a
  pr2 (lift-family-of-fibers a) = refl
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

    ev-lift-family-of-fibers :
      ((y : B) (z : fiber f y) → C y z) → ((x : A) → C (f x) (x , refl))
    ev-lift-family-of-fibers = ev-lift f (fiber f) (lift-family-of-fibers f)

    inv-ev-lift-family-of-fibers :
      ((x : A) → C (f x) (x , refl)) → ((y : B) (z : fiber f y) → C y z)
    inv-ev-lift-family-of-fibers h .(f x) (x , refl) = h x

    is-section-inv-ev-lift-family-of-fibers :
      (ev-lift-family-of-fibers ∘ inv-ev-lift-family-of-fibers) ~ id
    is-section-inv-ev-lift-family-of-fibers h = refl

    is-retraction-inv-ev-lift-family-of-fibers' :
      (h : (y : B) (z : fiber f y) → C y z) (y : B) →
      (inv-ev-lift-family-of-fibers (ev-lift-family-of-fibers h) y) ~ (h y)
    is-retraction-inv-ev-lift-family-of-fibers' h .(f z) (z , refl) = refl

    is-retraction-inv-ev-lift-family-of-fibers :
      (inv-ev-lift-family-of-fibers ∘ ev-lift-family-of-fibers) ~ id
    is-retraction-inv-ev-lift-family-of-fibers h =
      eq-htpy (eq-htpy ∘ is-retraction-inv-ev-lift-family-of-fibers' h)

    is-equiv-inv-ev-lift-family-of-fibers :
      is-equiv inv-ev-lift-family-of-fibers
    is-equiv-inv-ev-lift-family-of-fibers =
      is-equiv-is-invertible
        ( ev-lift-family-of-fibers)
        ( is-retraction-inv-ev-lift-family-of-fibers)
        ( is-section-inv-ev-lift-family-of-fibers)

    inv-equiv-dependent-universal-property-family-of-fibers :
      ((x : A) → C (f x) (x , refl)) ≃ ((y : B) (z : fiber f y) → C y z)
    pr1 inv-equiv-dependent-universal-property-family-of-fibers =
      inv-ev-lift-family-of-fibers
    pr2 inv-equiv-dependent-universal-property-family-of-fibers =
      is-equiv-inv-ev-lift-family-of-fibers

  dependent-universal-property-family-of-fibers-fiber :
    dependent-universal-property-family-of-fibers f
      ( fiber f)
      ( lift-family-of-fibers f)
  dependent-universal-property-family-of-fibers-fiber C =
    is-equiv-is-invertible
      ( inv-ev-lift-family-of-fibers C)
      ( is-section-inv-ev-lift-family-of-fibers C)
      ( is-retraction-inv-ev-lift-family-of-fibers C)

  equiv-dependent-universal-property-family-of-fibers :
    {l3 : Level} (C : (y : B) (z : fiber f y) → UU l3) →
    ((y : B) (z : fiber f y) → C y z) ≃ ((x : A) → C (f x) (x , refl))
  pr1 (equiv-dependent-universal-property-family-of-fibers C) =
    ev-lift-family-of-fibers C
  pr2 (equiv-dependent-universal-property-family-of-fibers C) =
    dependent-universal-property-family-of-fibers-fiber C
```

### The family of fibers of a map satisfies the dependent universal property of the family of fibers of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  universal-property-family-of-fibers-fiber :
    universal-property-family-of-fibers f (fiber f) (lift-family-of-fibers f)
  universal-property-family-of-fibers-fiber C =
    dependent-universal-property-family-of-fibers-fiber f (λ y _ → C y)

  equiv-universal-property-family-of-fibers :
    {l3 : Level} (C : B → UU l3) →
    ((y : B) → fiber f y → C y) ≃ ((x : A) → C (f x))
  equiv-universal-property-family-of-fibers C =
    equiv-dependent-universal-property-family-of-fibers f (λ y _ → C y)
```

### The inverse equivalence of the universal property of the family of fibers of a map

The inverse of the equivalence `equiv-universal-property-family-of-fibers` has a reasonably nice definition, so we also record it here.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  inv-equiv-universal-property-family-of-fibers :
    ((x : A) → C (f x)) ≃ ((y : B) → fiber f y → C y)
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
      ( ev-lift-family-of-fibers f (λ b _ → C b))
      ( map-Π (λ b u _ → u))
      ( is-equiv-map-Π-is-fiberwise-equiv H)
      ( universal-property-family-of-fibers-fiber f C)
```
