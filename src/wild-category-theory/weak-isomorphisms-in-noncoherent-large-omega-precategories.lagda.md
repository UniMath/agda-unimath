# Weak isomorphisms in noncoherent large ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.weak-isomorphisms-in-noncoherent-large-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import wild-category-theory.noncoherent-large-omega-precategories
open import wild-category-theory.weak-isomorphisms-in-noncoherent-omega-precategories
```

</details>

## Idea

Consider a
[noncoherent large ω-precategory](wild-category-theory.noncoherent-large-omega-precategories.md)
`𝒞`. A
{{#concept "weak isomorphism" Disambiguation="in noncoherent large ω-precategories" Agda=is-weak-iso-Noncoherent-Large-ω-Precategory}}
in `𝒞` is a morphism `f : x → y` in `𝒞` [equipped](foundation.structure.md) with

- a morphism `s : y → x`
- a $2$-morphism `is-split-epi : f ∘ s → id`, where `∘` and `id` denote
  composition of morphisms and the identity morphism given by the transitive and
  reflexive structure on the underlying
  [globular type](globular-types.globular-types.md), respectively
- a proof `is-weak-iso-is-split-epi : is-weak-iso is-split-epi`, which shows
  that the above $2$-morphism is itself a weak isomorphism
- a morphism `r : y → x`
- a $2$-morphism `is-split-mono : r ∘ f → id`
- a proof `is-weak-iso-is-split-mono : is-weak-iso is-split-mono`.

This definition of a weak isomorphism mirrors the definition of
[biinvertible maps](foundation-core.equivalences.md) between types.

Note that a noncoherent large ω-precategory is the most general setting that
allows us to _define_ weak isomorphisms in large wild categories, but because of
the missing coherences, we cannot show any of the expected properties. For
example we cannot show that all identities are weak isomorphisms, or that weak
isomorphisms compose.

## Definitions

### The predicate on morphisms of being weak isomorphisms

```agda
record
  is-weak-iso-Noncoherent-Large-ω-Precategory
  {α : Level → Level} {β : Level → Level → Level}
  (𝒞 : Noncoherent-Large-ω-Precategory α β)
  {l1 : Level} {x : obj-Noncoherent-Large-ω-Precategory 𝒞 l1}
  {l2 : Level} {y : obj-Noncoherent-Large-ω-Precategory 𝒞 l2}
  (f : hom-Noncoherent-Large-ω-Precategory 𝒞 x y)
  : UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  where
  field
    hom-section-is-weak-iso-Noncoherent-Large-ω-Precategory :
      hom-Noncoherent-Large-ω-Precategory 𝒞 y x
    is-split-epi-is-weak-iso-Noncoherent-Large-ω-Precategory :
      2-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
          ( f)
          ( hom-section-is-weak-iso-Noncoherent-Large-ω-Precategory))
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
    is-weak-iso-is-split-epi-is-weak-iso-Noncoherent-Large-ω-Precategory :
      is-weak-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
          ( 𝒞)
          ( y)
          ( y))
        ( is-split-epi-is-weak-iso-Noncoherent-Large-ω-Precategory)

    hom-retraction-is-weak-iso-Noncoherent-Large-ω-Precategory :
      hom-Noncoherent-Large-ω-Precategory 𝒞 y x
    is-split-mono-is-weak-iso-Noncoherent-Large-ω-Precategory :
      2-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
          ( hom-retraction-is-weak-iso-Noncoherent-Large-ω-Precategory)
          ( f))
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
    is-weak-iso-is-split-mono-is-weak-iso-Noncoherent-Large-ω-Precategory :
      is-weak-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
          ( 𝒞)
          ( x)
          ( x))
        ( is-split-mono-is-weak-iso-Noncoherent-Large-ω-Precategory)

open is-weak-iso-Noncoherent-Large-ω-Precategory public
```

### Weak isomorphisms in a noncoherent large ω-precategory

```agda
weak-iso-Noncoherent-Large-ω-Precategory :
  {α : Level → Level} {β : Level → Level → Level}
  (𝒞 : Noncoherent-Large-ω-Precategory α β)
  {l1 : Level} (x : obj-Noncoherent-Large-ω-Precategory 𝒞 l1)
  {l2 : Level} (y : obj-Noncoherent-Large-ω-Precategory 𝒞 l2) →
  UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
weak-iso-Noncoherent-Large-ω-Precategory 𝒞 x y =
  Σ ( hom-Noncoherent-Large-ω-Precategory 𝒞 x y)
    ( is-weak-iso-Noncoherent-Large-ω-Precategory 𝒞)
```

### Components of a weak isomorphism in a noncoherent large ω-precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {𝒞 : Noncoherent-Large-ω-Precategory α β}
  {l1 : Level} {x : obj-Noncoherent-Large-ω-Precategory 𝒞 l1}
  {l2 : Level} {y : obj-Noncoherent-Large-ω-Precategory 𝒞 l2}
  (f : weak-iso-Noncoherent-Large-ω-Precategory 𝒞 x y)
  where

  hom-weak-iso-Noncoherent-Large-ω-Precategory :
    hom-Noncoherent-Large-ω-Precategory 𝒞 x y
  hom-weak-iso-Noncoherent-Large-ω-Precategory = pr1 f

  is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory :
    is-weak-iso-Noncoherent-Large-ω-Precategory 𝒞
      ( hom-weak-iso-Noncoherent-Large-ω-Precategory)
  is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory = pr2 f

  hom-section-weak-iso-Noncoherent-Large-ω-Precategory :
    hom-Noncoherent-Large-ω-Precategory 𝒞 y x
  hom-section-weak-iso-Noncoherent-Large-ω-Precategory =
    hom-section-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory :
    2-hom-Noncoherent-Large-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-section-weak-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory =
    is-split-epi-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  is-weak-iso-is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory :
    is-weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory)
  is-weak-iso-is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-is-split-epi-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  weak-iso-is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory :
    weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-section-weak-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  pr1 weak-iso-is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory =
    is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory
  pr2 weak-iso-is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-is-split-epi-weak-iso-Noncoherent-Large-ω-Precategory

  hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory :
    hom-Noncoherent-Large-ω-Precategory 𝒞 y x
  hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory =
    hom-retraction-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory :
    2-hom-Noncoherent-Large-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory =
    is-split-mono-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  is-weak-iso-is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory :
    is-weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory)
  is-weak-iso-is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-is-split-mono-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  weak-iso-is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory :
    weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  pr1 weak-iso-is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory =
    is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory
  pr2 weak-iso-is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-is-split-mono-weak-iso-Noncoherent-Large-ω-Precategory
```

## See also

- [Weak isomorphisms in noncoherent ω-precategories](wild-category-theory.weak-isomorphisms-in-noncoherent-omega-precategories.md)
