# The universal property of fibers of maps

```agda
module foundation.universal-property-family-of-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.subtype-identity-principle
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universal-property-family-of-fibers-of-maps
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

## Properties

### Fibers are uniquely unique

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} (F : B → UU l3)
  (δ : (a : A) → F (f a)) (P : B → UU l4) (γ : (a : A) → P (f a))
  where

  section-preserving-fiberwise-map-fiber : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-preserving-fiberwise-map-fiber =
    Σ ((b : B) → F b → P b) (λ h → ev-lift f F δ h ~ γ)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)} {P : B → UU l4} {γ : (a : A) → P (f a)}
  where

  fiberwise-map-section-preserving-fiberwise-map-fiber :
    section-preserving-fiberwise-map-fiber F δ P γ → (b : B) → F b → P b
  fiberwise-map-section-preserving-fiberwise-map-fiber = pr1

  preserves-section-section-preserving-fiberwise-map-fiber :
    (w : section-preserving-fiberwise-map-fiber F δ P γ) →
    ev-lift f F δ (fiberwise-map-section-preserving-fiberwise-map-fiber w) ~ γ
  preserves-section-section-preserving-fiberwise-map-fiber = pr2

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)}
  where

  id-section-preserving-fiberwise-map-fiber :
    section-preserving-fiberwise-map-fiber F δ F δ
  pr1 id-section-preserving-fiberwise-map-fiber b = id
  pr2 id-section-preserving-fiberwise-map-fiber = refl-htpy

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {f : A → B} {F : B → UU l3}
  {δ : (a : A) → F (f a)} {P : B → UU l4} {γ : (a : A) → P (f a)}
  {Q : B → UU l5} {η : (a : A) → Q (f a)}
  where

  dependent-comp-section-preserving-fiberwise-map-fiber :
    ( section-preserving-fiberwise-map-fiber P γ Q η) →
    ( section-preserving-fiberwise-map-fiber F δ P γ) →
    ( section-preserving-fiberwise-map-fiber F δ Q η)
  pr1 (dependent-comp-section-preserving-fiberwise-map-fiber g h) =
    dependent-comp
      ( fiberwise-map-section-preserving-fiberwise-map-fiber g)
      ( fiberwise-map-section-preserving-fiberwise-map-fiber h)
  pr2 (dependent-comp-section-preserving-fiberwise-map-fiber g h) a =
    ( ap
      ( (fiberwise-map-section-preserving-fiberwise-map-fiber g) (f a))
      ( preserves-section-section-preserving-fiberwise-map-fiber h a)) ∙
    ( preserves-section-section-preserving-fiberwise-map-fiber g a)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (u : universal-property-family-of-fibers f F δ)
  (P : B → UU l4) (γ : (a : A) → P (f a))
  where

  uniqueness-fiberwise-map-universal-property-family-of-fibers :
    is-contr (section-preserving-fiberwise-map-fiber F δ P γ)
  uniqueness-fiberwise-map-universal-property-family-of-fibers =
    is-contr-equiv
      ( fiber (ev-lift f F δ) γ)
      ( equiv-tot
        ( λ h → equiv-eq-htpy))
      ( is-contr-map-is-equiv (u P) γ)

  section-preserving-fiberwise-map-universal-property-family-of-fibers :
    section-preserving-fiberwise-map-fiber F δ P γ
  section-preserving-fiberwise-map-universal-property-family-of-fibers =
    ( center uniqueness-fiberwise-map-universal-property-family-of-fibers)

  fiberwise-map-universal-property-family-of-fibers :
    (b : B) → F b → P b
  fiberwise-map-universal-property-family-of-fibers =
    fiberwise-map-section-preserving-fiberwise-map-fiber
      section-preserving-fiberwise-map-universal-property-family-of-fibers

  preserves-section-fiberwise-map-universal-property-family-of-fibers :
    (ev-lift f F δ fiberwise-map-universal-property-family-of-fibers) ~ γ
  preserves-section-fiberwise-map-universal-property-family-of-fibers =
    preserves-section-section-preserving-fiberwise-map-fiber
      section-preserving-fiberwise-map-universal-property-family-of-fibers

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (u : universal-property-family-of-fibers f F δ)
  (P : B → UU l4) (γ : (a : A) → P (f a))
  (u' : universal-property-family-of-fibers f P γ)
  where

  dependent-comp-retraction-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers :
    ( dependent-comp-section-preserving-fiberwise-map-fiber
      ( section-preserving-fiberwise-map-universal-property-family-of-fibers
        f P γ u' F δ)
      ( section-preserving-fiberwise-map-universal-property-family-of-fibers
        ( f)
        ( F)
        ( δ)
        ( u)
        ( P)
        ( γ))) ＝
    ( id-section-preserving-fiberwise-map-fiber)
  dependent-comp-retraction-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers =
    eq-is-contr
      ( uniqueness-fiberwise-map-universal-property-family-of-fibers
        f F δ u F δ)

  dependent-comp-section-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers :
    ( dependent-comp-section-preserving-fiberwise-map-fiber
      ( section-preserving-fiberwise-map-universal-property-family-of-fibers
        f F δ u P γ))
      ( section-preserving-fiberwise-map-universal-property-family-of-fibers
        ( f)
        ( P)
        ( γ)
        ( u')
        ( F)
        ( δ)) ＝
    ( id-section-preserving-fiberwise-map-fiber)
  dependent-comp-section-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers =
    eq-is-contr
      ( uniqueness-fiberwise-map-universal-property-family-of-fibers
        f P γ u' P γ)

  is-fiberwise-retraction-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers :
    (b : B) →
    ( ( fiberwise-map-universal-property-family-of-fibers f P γ u' F δ b) ∘
    ( fiberwise-map-universal-property-family-of-fibers f F δ u P γ b)) ~
    ( id)
  is-fiberwise-retraction-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers
    b =
    htpy-eq
      ( htpy-eq
        ( ap
          ( pr1)
          ( dependent-comp-retraction-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers))
        ( b))

  is-fiberwise-section-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers :
    (b : B) →
    ( ( fiberwise-map-universal-property-family-of-fibers f F δ u P γ b) ∘
    ( fiberwise-map-universal-property-family-of-fibers f P γ u' F δ b)) ~
    ( id)
  is-fiberwise-section-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers
    b =
    htpy-eq
      ( htpy-eq
        ( ap
          ( pr1)
          ( dependent-comp-section-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers))
        ( b))

  is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers :
    is-fiberwise-equiv
      ( fiberwise-map-universal-property-family-of-fibers f F δ u P γ)
  is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers
    b =
    is-equiv-is-invertible
      ( fiberwise-map-section-preserving-fiberwise-map-fiber
        ( section-preserving-fiberwise-map-universal-property-family-of-fibers
          ( f)
          ( P)
          ( γ)
          ( u')
          ( F)
          ( δ))
        ( b))
      ( is-fiberwise-section-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers
        ( b))
      ( is-fiberwise-retraction-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers
        ( b))

  uniquely-unique-fiberwise-map-universal-property-family-of-fibers :
    is-contr
      ( Σ (fiberwise-equiv F P)
        ( λ h → (ev-lift f F δ (map-fiberwise-equiv h)) ~ γ))
  uniquely-unique-fiberwise-map-universal-property-family-of-fibers =
    is-torsorial-Eq-subtype
      ( uniqueness-fiberwise-map-universal-property-family-of-fibers
        f F δ u P γ)
      ( is-property-is-fiberwise-equiv)
      ( fiberwise-map-universal-property-family-of-fibers f F δ u P γ)
      ( preserves-section-fiberwise-map-universal-property-family-of-fibers
        f F δ u P γ)
      ( is-fiberwise-equiv-fiberwise-map-universal-property-family-of-fibers-universal-property-family-of-fibers)

  section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers :
    Σ (fiberwise-equiv F P)
      ( λ h → (ev-lift f F δ (map-fiberwise-equiv h)) ~ γ)
  section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers =
    center uniquely-unique-fiberwise-map-universal-property-family-of-fibers

  fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers :
    fiberwise-equiv F P
  fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers =
    pr1
      ( section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers)

  preserves-section-fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers :
    (ev-lift
      ( f)
      ( F)
      ( δ)
      ( map-fiberwise-equiv
        ( fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers))) ~
    ( γ)
  preserves-section-fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers =
    pr2
      ( section-preserving-fiberwise-equiv-unique-fiberwise-map-universal-property-family-of-fibers)
```
