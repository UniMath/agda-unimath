# Isomorphisms in noncoherent large wild higher precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.isomorphisms-in-noncoherent-large-wild-higher-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import wild-category-theory.isomorphisms-in-noncoherent-wild-higher-precategories
open import wild-category-theory.noncoherent-large-wild-higher-precategories
```

</details>

## Idea

Consider a
[noncoherent large wild higher precategory](wild-category-theory.noncoherent-large-wild-higher-precategories.md)
𝒞. An
{{#concept "isomorphism" Disambiguation="in noncoherent large wild higher precategories" Agda=is-iso-Noncoherent-Large-Wild-Higher-Precategory}}
in 𝒞 is a morphism `f : x → y` in 𝒞 [equipped](foundation.structure.md) with

- a morphism `s : y → x`
- a $2$-morphism `is-split-epi : f ∘ s → id`, where `∘` and `id` denote
  composition of morphisms and the identity morphism given by the transitive and
  reflexive structure on the underlying
  [globular type](structured-types.globular-types.md), respectively
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

Note that a noncoherent large wild higher precategory is the most general
setting that allows us to _define_ isomorphisms in large wild categories, but
because of the missing coherences, we cannot show any of the expected
properties. For example we cannot show that all identities are isomorphisms, or
that isomorphisms compose.

## Definitions

### The predicate on morphisms of being an isomorphism

```agda
record
  is-iso-Noncoherent-Large-Wild-Higher-Precategory
  {α : Level → Level} {β : Level → Level → Level}
  (𝒞 : Noncoherent-Large-Wild-Higher-Precategory α β)
  {l1 : Level} {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒞 l1}
  {l2 : Level} {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒞 l2}
  (f : hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞 x y)
  : UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  where
  field
    hom-section-is-iso-Noncoherent-Large-Wild-Higher-Precategory :
      hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞 y x
    is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategory :
      2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
          ( f)
          ( hom-section-is-iso-Noncoherent-Large-Wild-Higher-Precategory))
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞)
    is-iso-is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategory :
      is-iso-Noncoherent-Wild-Higher-Precategory
        ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
          ( 𝒞)
          ( y)
          ( y))
        ( is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategory)

    hom-retraction-is-iso-Noncoherent-Large-Wild-Higher-Precategory :
      hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞 y x
    is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategory :
      2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
          ( hom-retraction-is-iso-Noncoherent-Large-Wild-Higher-Precategory)
          ( f))
        ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞)
    is-iso-is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategory :
      is-iso-Noncoherent-Wild-Higher-Precategory
        ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
          ( 𝒞)
          ( x)
          ( x))
        ( is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategory)

open is-iso-Noncoherent-Large-Wild-Higher-Precategory public
```

### Isomorphisms in a noncoherent large wild higher precategory

```agda
iso-Noncoherent-Large-Wild-Higher-Precategory :
  {α : Level → Level} {β : Level → Level → Level}
  (𝒞 : Noncoherent-Large-Wild-Higher-Precategory α β)
  {l1 : Level} (x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒞 l1)
  {l2 : Level} (y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒞 l2) →
  UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
iso-Noncoherent-Large-Wild-Higher-Precategory 𝒞 x y =
  Σ ( hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞 x y)
    ( is-iso-Noncoherent-Large-Wild-Higher-Precategory 𝒞)
```

### Components of an isomorphism in a noncoherent large wild higher precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {𝒞 : Noncoherent-Large-Wild-Higher-Precategory α β}
  {l1 : Level} {x : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒞 l1}
  {l2 : Level} {y : obj-Noncoherent-Large-Wild-Higher-Precategory 𝒞 l2}
  (f : iso-Noncoherent-Large-Wild-Higher-Precategory 𝒞 x y)
  where

  hom-iso-Noncoherent-Large-Wild-Higher-Precategory :
    hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞 x y
  hom-iso-Noncoherent-Large-Wild-Higher-Precategory = pr1 f

  is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory :
    is-iso-Noncoherent-Large-Wild-Higher-Precategory 𝒞
      ( hom-iso-Noncoherent-Large-Wild-Higher-Precategory)
  is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory = pr2 f

  hom-section-iso-Noncoherent-Large-Wild-Higher-Precategory :
    hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞 y x
  hom-section-iso-Noncoherent-Large-Wild-Higher-Precategory =
    hom-section-is-iso-Noncoherent-Large-Wild-Higher-Precategory
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory)

  is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory :
    2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategory)
        ( hom-section-iso-Noncoherent-Large-Wild-Higher-Precategory))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞)
  is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategory
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory)

  is-iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory :
    is-iso-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory)
  is-iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-iso-is-split-epi-is-iso-Noncoherent-Large-Wild-Higher-Precategory
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory)

  iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory :
    iso-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategory)
        ( hom-section-iso-Noncoherent-Large-Wild-Higher-Precategory))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞)
  pr1 iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory
  pr2 iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-iso-is-split-epi-iso-Noncoherent-Large-Wild-Higher-Precategory

  hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategory :
    hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞 y x
  hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategory =
    hom-retraction-is-iso-Noncoherent-Large-Wild-Higher-Precategory
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory)

  is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory :
    2-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategory)
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategory))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞)
  is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategory
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory)

  is-iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory :
    is-iso-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory)
  is-iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-iso-is-split-mono-is-iso-Noncoherent-Large-Wild-Higher-Precategory
      ( is-iso-hom-iso-Noncoherent-Large-Wild-Higher-Precategory)

  iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory :
    iso-Noncoherent-Wild-Higher-Precategory
      ( hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( comp-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞
        ( hom-retraction-iso-Noncoherent-Large-Wild-Higher-Precategory)
        ( hom-iso-Noncoherent-Large-Wild-Higher-Precategory))
      ( id-hom-Noncoherent-Large-Wild-Higher-Precategory 𝒞)
  pr1 iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory
  pr2 iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory =
    is-iso-is-split-mono-iso-Noncoherent-Large-Wild-Higher-Precategory
```

## See also

- [Isomorphisms in noncoherent wild higher precategories](wild-category-theory.isomorphisms-in-noncoherent-wild-higher-precategories.md)
