# Weak isomorphisms in noncoherent ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.weak-isomorphisms-in-noncoherent-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

Consider a
[noncoherent ω-precategory](wild-category-theory.noncoherent-omega-precategories.md)
`𝒞`. A
{{#concept "weak isomorphism" Disambiguation="in noncoherent ω-precategories" Agda=is-weak-iso-Noncoherent-ω-Precategory}}
in `𝒞` is a morphism `f : x → y` in `𝒞` [equipped](foundation.structure.md) with

- a morphism `s : y → x`
- a $2$-morphism `ε : f ∘ s → id`, where `∘` and `id` denote composition of
  morphisms and the identity morphism given by the transitive and reflexive
  structure on the underlying [globular type](globular-types.globular-types.md),
  respectively
- a proof `is-weak-iso ε`, which shows that the above $2$-morphism is itself a
  weak isomorphism
- a morphism `r : y → x`
- a $2$-morphism `η : id → r ∘ f`
- a proof `is-weak-iso η`.

This definition of a weak isomorphism mirrors the definition of
[biinvertible maps](foundation-core.equivalences.md) between types.

Note that a noncoherent ω-precategory is the most general setting that allows us
to _define_ weak isomorphisms in wild categories, but because of the missing
coherences, we cannot show any of the expected properties. For example we cannot
show that all identities are weak isomorphisms, or that weak isomorphisms
compose.

## Definitions

### The predicate on morphisms of being weak isomorphisms

```agda
record
  is-weak-iso-Noncoherent-ω-Precategory
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Precategory l1 l2)
  {x y : obj-Noncoherent-ω-Precategory 𝒞}
  (f : hom-Noncoherent-ω-Precategory 𝒞 x y) : UU l2
  where
  coinductive
  field
    hom-section-is-weak-iso-Noncoherent-ω-Precategory :
      hom-Noncoherent-ω-Precategory 𝒞 y x
    is-split-epi-is-weak-iso-Noncoherent-ω-Precategory :
      2-hom-Noncoherent-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-ω-Precategory 𝒞
          ( f)
          ( hom-section-is-weak-iso-Noncoherent-ω-Precategory))
        ( id-hom-Noncoherent-ω-Precategory 𝒞)
    is-weak-iso-is-split-epi-is-weak-iso-Noncoherent-ω-Precategory :
      is-weak-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
          ( 𝒞)
          ( y)
          ( y))
        ( is-split-epi-is-weak-iso-Noncoherent-ω-Precategory)

    hom-retraction-is-weak-iso-Noncoherent-ω-Precategory :
      hom-Noncoherent-ω-Precategory 𝒞 y x
    is-split-mono-is-weak-iso-Noncoherent-ω-Precategory :
      2-hom-Noncoherent-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-ω-Precategory 𝒞
          ( hom-retraction-is-weak-iso-Noncoherent-ω-Precategory)
          ( f))
        ( id-hom-Noncoherent-ω-Precategory 𝒞)
    is-weak-iso-is-split-mono-is-weak-iso-Noncoherent-ω-Precategory :
      is-weak-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
          ( 𝒞)
          ( x)
          ( x))
        ( is-split-mono-is-weak-iso-Noncoherent-ω-Precategory)

open is-weak-iso-Noncoherent-ω-Precategory public
```

### Weak isomorphisms in a noncoherent ω-precategory

```agda
weak-iso-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Precategory l1 l2)
  (x y : obj-Noncoherent-ω-Precategory 𝒞) →
  UU l2
weak-iso-Noncoherent-ω-Precategory 𝒞 x y =
  Σ ( hom-Noncoherent-ω-Precategory 𝒞 x y)
    ( is-weak-iso-Noncoherent-ω-Precategory 𝒞)
```

### Components of a weak isomorphism in a noncoherent ω-precategory

```agda
module _
  {l1 l2 : Level} {𝒞 : Noncoherent-ω-Precategory l1 l2}
  {x y : obj-Noncoherent-ω-Precategory 𝒞}
  (f : weak-iso-Noncoherent-ω-Precategory 𝒞 x y)
  where

  hom-weak-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 x y
  hom-weak-iso-Noncoherent-ω-Precategory = pr1 f

  is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory :
    is-weak-iso-Noncoherent-ω-Precategory 𝒞
      ( hom-weak-iso-Noncoherent-ω-Precategory)
  is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory = pr2 f

  hom-section-weak-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 y x
  hom-section-weak-iso-Noncoherent-ω-Precategory =
    hom-section-is-weak-iso-Noncoherent-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory)

  is-split-epi-weak-iso-Noncoherent-ω-Precategory :
    2-hom-Noncoherent-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-weak-iso-Noncoherent-ω-Precategory)
        ( hom-section-weak-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  is-split-epi-weak-iso-Noncoherent-ω-Precategory =
    is-split-epi-is-weak-iso-Noncoherent-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory)

  is-weak-iso-is-split-epi-weak-iso-Noncoherent-ω-Precategory :
    is-weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( is-split-epi-weak-iso-Noncoherent-ω-Precategory)
  is-weak-iso-is-split-epi-weak-iso-Noncoherent-ω-Precategory =
    is-weak-iso-is-split-epi-is-weak-iso-Noncoherent-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory)

  iso-is-split-epi-weak-iso-Noncoherent-ω-Precategory :
    weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-weak-iso-Noncoherent-ω-Precategory)
        ( hom-section-weak-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  pr1 iso-is-split-epi-weak-iso-Noncoherent-ω-Precategory =
    is-split-epi-weak-iso-Noncoherent-ω-Precategory
  pr2 iso-is-split-epi-weak-iso-Noncoherent-ω-Precategory =
    is-weak-iso-is-split-epi-weak-iso-Noncoherent-ω-Precategory

  hom-retraction-weak-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 y x
  hom-retraction-weak-iso-Noncoherent-ω-Precategory =
    hom-retraction-is-weak-iso-Noncoherent-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory)

  is-split-mono-weak-iso-Noncoherent-ω-Precategory :
    2-hom-Noncoherent-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-retraction-weak-iso-Noncoherent-ω-Precategory)
        ( hom-weak-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  is-split-mono-weak-iso-Noncoherent-ω-Precategory =
    is-split-mono-is-weak-iso-Noncoherent-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory)

  is-weak-iso-is-split-mono-weak-iso-Noncoherent-ω-Precategory :
    is-weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( is-split-mono-weak-iso-Noncoherent-ω-Precategory)
  is-weak-iso-is-split-mono-weak-iso-Noncoherent-ω-Precategory =
    is-weak-iso-is-split-mono-is-weak-iso-Noncoherent-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-ω-Precategory)

  iso-is-split-mono-weak-iso-Noncoherent-ω-Precategory :
    weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-retraction-weak-iso-Noncoherent-ω-Precategory)
        ( hom-weak-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  pr1 iso-is-split-mono-weak-iso-Noncoherent-ω-Precategory =
    is-split-mono-weak-iso-Noncoherent-ω-Precategory
  pr2 iso-is-split-mono-weak-iso-Noncoherent-ω-Precategory =
    is-weak-iso-is-split-mono-weak-iso-Noncoherent-ω-Precategory
```

## See also

- [Weak isomorphisms in noncoherent large ω-precategories](wild-category-theory.weak-isomorphisms-in-noncoherent-large-omega-precategories.md)
