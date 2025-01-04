# Isomorphisms in noncoherent ω-precategories

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
[noncoherent wild higher precategory](wild-category-theory.noncoherent-omega-precategories.md)
`𝒞`. An
{{#concept "isomorphism" Disambiguation="in noncoherent ω-precategories" Agda=is-iso-Noncoherent-ω-Precategory}}
in `𝒞` is a morphism `f : x → y` in `𝒞` [equipped](foundation.structure.md) with

- a morphism `s : y → x`
- a $2$-morphism `is-split-epi : f ∘ s → id`, where `∘` and `id` denote
  composition of morphisms and the identity morphism given by the transitive and
  reflexive structure on the underlying
  [globular type](globular-types.globular-types.md), respectively
- a proof `is-iso-is-split-epi : is-iso is-split-epi`, which shows that the
  above $2$-morphism is itself an isomorphism
- a morphism `r : y → x`
- a $2$-morphism `is-split-mono : r ∘ f → id`
- a proof `is-iso-is-split-mono : is-iso is-split-mono`.

This definition of an isomorphism mirrors the definition of
[biinvertible maps](foundation-core.equivalences.md) between types.

It would be in the spirit of the library to first define what split epimorphisms
and split monomorphisms are, and then define isomorphisms as those morphisms
which are both. When attempting that definition, one runs into the problem that
the $2$-morphisms in the definitions should still be isomorphisms.
Alternatively, one could require that the morphisms compose to the identity
morphism up to [identification](foundation-core.identity-types.md) of morphisms,
instead of up to a higher isomorphism.

Note that a noncoherent wild higher precategory is the most general setting that
allows us to _define_ isomorphisms in wild categories, but because of the
missing coherences, we cannot show any of the expected properties. For example
we cannot show that all identities are isomorphisms, or that isomorphisms
compose.

## Definitions

### The predicate on a morphism of being an isomorphism

```agda
record
  is-iso-Noncoherent-ω-Precategory
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Precategory l1 l2)
  {x y : obj-Noncoherent-ω-Precategory 𝒞}
  (f : hom-Noncoherent-ω-Precategory 𝒞 x y) : UU l2
  where
  coinductive
  field
    hom-section-is-iso-Noncoherent-ω-Precategory :
      hom-Noncoherent-ω-Precategory 𝒞 y x
    is-split-epi-is-iso-Noncoherent-ω-Precategory :
      2-hom-Noncoherent-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-ω-Precategory 𝒞
          ( f)
          ( hom-section-is-iso-Noncoherent-ω-Precategory))
        ( id-hom-Noncoherent-ω-Precategory 𝒞)
    is-iso-is-split-epi-is-iso-Noncoherent-ω-Precategory :
      is-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
          ( 𝒞)
          ( y)
          ( y))
        ( is-split-epi-is-iso-Noncoherent-ω-Precategory)

    hom-retraction-is-iso-Noncoherent-ω-Precategory :
      hom-Noncoherent-ω-Precategory 𝒞 y x
    is-split-mono-is-iso-Noncoherent-ω-Precategory :
      2-hom-Noncoherent-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-ω-Precategory 𝒞
          ( hom-retraction-is-iso-Noncoherent-ω-Precategory)
          ( f))
        ( id-hom-Noncoherent-ω-Precategory 𝒞)
    is-iso-is-split-mono-is-iso-Noncoherent-ω-Precategory :
      is-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
          ( 𝒞)
          ( x)
          ( x))
        ( is-split-mono-is-iso-Noncoherent-ω-Precategory)

open is-iso-Noncoherent-ω-Precategory public
```

### Isomorphisms in a noncoherent wild higher precategory

```agda
iso-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Precategory l1 l2)
  (x y : obj-Noncoherent-ω-Precategory 𝒞) →
  UU l2
iso-Noncoherent-ω-Precategory 𝒞 x y =
  Σ ( hom-Noncoherent-ω-Precategory 𝒞 x y)
    ( is-iso-Noncoherent-ω-Precategory 𝒞)
```

### Components of an isomorphism in a noncoherent wild higher precategory

```agda
module _
  {l1 l2 : Level} {𝒞 : Noncoherent-ω-Precategory l1 l2}
  {x y : obj-Noncoherent-ω-Precategory 𝒞}
  (f : iso-Noncoherent-ω-Precategory 𝒞 x y)
  where

  hom-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 x y
  hom-iso-Noncoherent-ω-Precategory = pr1 f

  is-iso-hom-iso-Noncoherent-ω-Precategory :
    is-iso-Noncoherent-ω-Precategory 𝒞
      ( hom-iso-Noncoherent-ω-Precategory)
  is-iso-hom-iso-Noncoherent-ω-Precategory = pr2 f

  hom-section-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 y x
  hom-section-iso-Noncoherent-ω-Precategory =
    hom-section-is-iso-Noncoherent-ω-Precategory
      ( is-iso-hom-iso-Noncoherent-ω-Precategory)

  is-split-epi-iso-Noncoherent-ω-Precategory :
    2-hom-Noncoherent-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-iso-Noncoherent-ω-Precategory)
        ( hom-section-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  is-split-epi-iso-Noncoherent-ω-Precategory =
    is-split-epi-is-iso-Noncoherent-ω-Precategory
      ( is-iso-hom-iso-Noncoherent-ω-Precategory)

  is-iso-is-split-epi-iso-Noncoherent-ω-Precategory :
    is-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( is-split-epi-iso-Noncoherent-ω-Precategory)
  is-iso-is-split-epi-iso-Noncoherent-ω-Precategory =
    is-iso-is-split-epi-is-iso-Noncoherent-ω-Precategory
      ( is-iso-hom-iso-Noncoherent-ω-Precategory)

  iso-is-split-epi-iso-Noncoherent-ω-Precategory :
    iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-iso-Noncoherent-ω-Precategory)
        ( hom-section-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  pr1 iso-is-split-epi-iso-Noncoherent-ω-Precategory =
    is-split-epi-iso-Noncoherent-ω-Precategory
  pr2 iso-is-split-epi-iso-Noncoherent-ω-Precategory =
    is-iso-is-split-epi-iso-Noncoherent-ω-Precategory

  hom-retraction-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 y x
  hom-retraction-iso-Noncoherent-ω-Precategory =
    hom-retraction-is-iso-Noncoherent-ω-Precategory
      ( is-iso-hom-iso-Noncoherent-ω-Precategory)

  is-split-mono-iso-Noncoherent-ω-Precategory :
    2-hom-Noncoherent-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-retraction-iso-Noncoherent-ω-Precategory)
        ( hom-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  is-split-mono-iso-Noncoherent-ω-Precategory =
    is-split-mono-is-iso-Noncoherent-ω-Precategory
      ( is-iso-hom-iso-Noncoherent-ω-Precategory)

  is-iso-is-split-mono-iso-Noncoherent-ω-Precategory :
    is-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( is-split-mono-iso-Noncoherent-ω-Precategory)
  is-iso-is-split-mono-iso-Noncoherent-ω-Precategory =
    is-iso-is-split-mono-is-iso-Noncoherent-ω-Precategory
      ( is-iso-hom-iso-Noncoherent-ω-Precategory)

  iso-is-split-mono-iso-Noncoherent-ω-Precategory :
    iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-retraction-iso-Noncoherent-ω-Precategory)
        ( hom-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  pr1 iso-is-split-mono-iso-Noncoherent-ω-Precategory =
    is-split-mono-iso-Noncoherent-ω-Precategory
  pr2 iso-is-split-mono-iso-Noncoherent-ω-Precategory =
    is-iso-is-split-mono-iso-Noncoherent-ω-Precategory
```

## See also

- [Isomorphisms in noncoherent large ω-precategories](wild-category-theory.isomorphisms-in-noncoherent-large-omega-precategories.md)
