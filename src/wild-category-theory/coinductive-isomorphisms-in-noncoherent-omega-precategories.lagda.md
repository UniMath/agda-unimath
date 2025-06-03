# Coinductive isomorphisms in noncoherent ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories where
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
{{#concept "coinductive isomorphism" Disambiguation="in noncoherent ω-precategories" Agda=is-coinductive-iso-Noncoherent-ω-Precategory}}
in `𝒞` is a morphism `f : 𝒞₁ x y` [equipped](foundation.structure.md) with,
coinductively,

- a morphism `s : 𝒞₁ y x`
- a $2$-morphism `η : 𝒞₂ id (f ∘ s)`
- a witness that `η` is itself a coinductive isomorphism
- another morphism `r : 𝒞₁ y x`
- a $2$-morphism `ε : 𝒞₂ (r ∘ f) id`
- a witness that `ε` is a coinductive isomorphism.

Thus, the specified data is a commuting diagram of the form

```text
  y ========= y
    \  ~⇓η  ∧   \
   s \     /f    \ r
      ∨   /  ~⇓ε  ∨
        x ========= x
```

where `η` and `ε` again are coinductive isomorphisms in their respective
hom-ω-categories.

> **Disclaimer.** We do not assert that the proposed definition of a coinductive
> isomorphism is fully coherent, and thus it may be subject to change in the
> future.

While a noncoherent ω-precategory is the most general setting that allows us to
_define_ coinductive isomorphisms, the missing coherences obstruct us from
showing many of the expected properties. For example, we cannot show that all
identities are coinductive isomorphisms or that coinductive isomorphisms
compose.

The concept of coinductive isomorphisms in ω-categories is strictly weaker than
the concept of _isomorphisms_. Indeed, the coindutive nature of this concept
allows us, in an informal sense, to indefinitely postpone constructing a witness
that `s` or `r` are "proper" inverses to `f`. To take an example, consider the
ω-category of spans and higher spans. In this ω-category every morphism is a
coinductive isomorphism since every morphism is a biadjoint, but not every
morphism is an isomorphism. Moreover, this ω-category is univalent with respect
to isomorphisms, but not with respect to all coinductive isomorphisms. More
generally, every morphism in an "ω-category with duals" is a coinductive
isomorphism {{#cite Cheng07}}.

## Definitions

### The predicate on morphisms of being coinductive isomorphisms

```agda
record
  is-coinductive-iso-Noncoherent-ω-Precategory
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Precategory l1 l2)
  {x y : obj-Noncoherent-ω-Precategory 𝒞}
  (f : hom-Noncoherent-ω-Precategory 𝒞 x y) : UU l2
  where
  coinductive
  field
    hom-section-is-coinductive-iso-Noncoherent-ω-Precategory :
      hom-Noncoherent-ω-Precategory 𝒞 y x

    unit-is-coinductive-iso-Noncoherent-ω-Precategory :
      2-hom-Noncoherent-ω-Precategory 𝒞
        ( id-hom-Noncoherent-ω-Precategory 𝒞)
        ( comp-hom-Noncoherent-ω-Precategory 𝒞
          ( f)
          ( hom-section-is-coinductive-iso-Noncoherent-ω-Precategory))

    is-coinductive-iso-unit-is-coinductive-iso-Noncoherent-ω-Precategory :
      is-coinductive-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
          ( 𝒞)
          ( y)
          ( y))
        ( unit-is-coinductive-iso-Noncoherent-ω-Precategory)

    hom-retraction-is-coinductive-iso-Noncoherent-ω-Precategory :
      hom-Noncoherent-ω-Precategory 𝒞 y x

    counit-is-coinductive-iso-Noncoherent-ω-Precategory :
      2-hom-Noncoherent-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-ω-Precategory 𝒞
          ( hom-retraction-is-coinductive-iso-Noncoherent-ω-Precategory)
          ( f))
        ( id-hom-Noncoherent-ω-Precategory 𝒞)

    is-coinductive-iso-counit-is-coinductive-iso-Noncoherent-ω-Precategory :
      is-coinductive-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
          ( 𝒞)
          ( x)
          ( x))
        ( counit-is-coinductive-iso-Noncoherent-ω-Precategory)

open is-coinductive-iso-Noncoherent-ω-Precategory public
```

### Coinductive isomorphisms in a noncoherent ω-precategory

```agda
coinductive-iso-Noncoherent-ω-Precategory :
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Precategory l1 l2)
  (x y : obj-Noncoherent-ω-Precategory 𝒞) →
  UU l2
coinductive-iso-Noncoherent-ω-Precategory 𝒞 x y =
  Σ ( hom-Noncoherent-ω-Precategory 𝒞 x y)
    ( is-coinductive-iso-Noncoherent-ω-Precategory 𝒞)
```

### Components of a coinductive isomorphism in a noncoherent ω-precategory

```agda
module _
  {l1 l2 : Level} {𝒞 : Noncoherent-ω-Precategory l1 l2}
  {x y : obj-Noncoherent-ω-Precategory 𝒞}
  (f : coinductive-iso-Noncoherent-ω-Precategory 𝒞 x y)
  where

  hom-coinductive-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 x y
  hom-coinductive-iso-Noncoherent-ω-Precategory = pr1 f

  is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory :
    is-coinductive-iso-Noncoherent-ω-Precategory 𝒞
      ( hom-coinductive-iso-Noncoherent-ω-Precategory)
  is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory = pr2 f

  hom-section-coinductive-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 y x
  hom-section-coinductive-iso-Noncoherent-ω-Precategory =
    hom-section-is-coinductive-iso-Noncoherent-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory)

  unit-coinductive-iso-Noncoherent-ω-Precategory :
    2-hom-Noncoherent-ω-Precategory 𝒞
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-coinductive-iso-Noncoherent-ω-Precategory)
        ( hom-section-coinductive-iso-Noncoherent-ω-Precategory))
  unit-coinductive-iso-Noncoherent-ω-Precategory =
    unit-is-coinductive-iso-Noncoherent-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory)

  is-coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory :
    is-coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( unit-coinductive-iso-Noncoherent-ω-Precategory)
  is-coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory =
    is-coinductive-iso-unit-is-coinductive-iso-Noncoherent-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory)

  coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory :
    coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-coinductive-iso-Noncoherent-ω-Precategory)
        ( hom-section-coinductive-iso-Noncoherent-ω-Precategory))
  pr1 coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory =
    unit-coinductive-iso-Noncoherent-ω-Precategory
  pr2 coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory =
    is-coinductive-iso-unit-coinductive-iso-Noncoherent-ω-Precategory

  hom-retraction-coinductive-iso-Noncoherent-ω-Precategory :
    hom-Noncoherent-ω-Precategory 𝒞 y x
  hom-retraction-coinductive-iso-Noncoherent-ω-Precategory =
    hom-retraction-is-coinductive-iso-Noncoherent-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory)

  counit-coinductive-iso-Noncoherent-ω-Precategory :
    2-hom-Noncoherent-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-retraction-coinductive-iso-Noncoherent-ω-Precategory)
        ( hom-coinductive-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  counit-coinductive-iso-Noncoherent-ω-Precategory =
    counit-is-coinductive-iso-Noncoherent-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory)

  is-coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory :
    is-coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( counit-coinductive-iso-Noncoherent-ω-Precategory)
  is-coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory =
    is-coinductive-iso-counit-is-coinductive-iso-Noncoherent-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-ω-Precategory)

  coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory :
    coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( comp-hom-Noncoherent-ω-Precategory 𝒞
        ( hom-retraction-coinductive-iso-Noncoherent-ω-Precategory)
        ( hom-coinductive-iso-Noncoherent-ω-Precategory))
      ( id-hom-Noncoherent-ω-Precategory 𝒞)
  pr1 coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory =
    counit-coinductive-iso-Noncoherent-ω-Precategory
  pr2 coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory =
    is-coinductive-iso-counit-coinductive-iso-Noncoherent-ω-Precategory
```

## See also

- [Coinductive isomorphisms in noncoherent large ω-precategories](wild-category-theory.coinductive-isomorphisms-in-noncoherent-large-omega-precategories.md)

## References

{{#bibliography}}
