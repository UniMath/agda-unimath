# Coinductive isomorphisms in noncoherent large ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.coinductive-isomorphisms-in-noncoherent-large-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories
open import wild-category-theory.noncoherent-large-omega-precategories
```

</details>

## Idea

Consider a
[noncoherent large ω-precategory](wild-category-theory.noncoherent-large-omega-precategories.md)
`𝒞`. A
{{#concept "coinductive isomorphism" Disambiguation="in noncoherent large ω-precategories" Agda=is-coinductive-iso-Noncoherent-Large-ω-Precategory}}
in `𝒞` is a morphism `f : x → y` in `𝒞` [equipped](foundation.structure.md) with

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
  is-coinductive-iso-Noncoherent-Large-ω-Precategory
  {α : Level → Level} {β : Level → Level → Level}
  (𝒞 : Noncoherent-Large-ω-Precategory α β)
  {l1 : Level} {x : obj-Noncoherent-Large-ω-Precategory 𝒞 l1}
  {l2 : Level} {y : obj-Noncoherent-Large-ω-Precategory 𝒞 l2}
  (f : hom-Noncoherent-Large-ω-Precategory 𝒞 x y)
  : UU (β l1 l1 ⊔ β l2 l1 ⊔ β l2 l2)
  where
  field
    hom-section-is-coinductive-iso-Noncoherent-Large-ω-Precategory :
      hom-Noncoherent-Large-ω-Precategory 𝒞 y x

    unit-is-coinductive-iso-Noncoherent-Large-ω-Precategory :
      2-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
          ( f)
          ( hom-section-is-coinductive-iso-Noncoherent-Large-ω-Precategory))

    is-coinductive-iso-unit-is-coinductive-iso-Noncoherent-Large-ω-Precategory :
      is-coinductive-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
          ( 𝒞)
          ( y)
          ( y))
        ( unit-is-coinductive-iso-Noncoherent-Large-ω-Precategory)

    hom-retraction-is-coinductive-iso-Noncoherent-Large-ω-Precategory :
      hom-Noncoherent-Large-ω-Precategory 𝒞 y x

    counit-is-coinductive-iso-Noncoherent-Large-ω-Precategory :
      2-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
          ( hom-retraction-is-coinductive-iso-Noncoherent-Large-ω-Precategory)
          ( f))
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)

    is-coinductive-iso-counit-is-coinductive-iso-Noncoherent-Large-ω-Precategory :
      is-coinductive-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
          ( 𝒞)
          ( x)
          ( x))
        ( counit-is-coinductive-iso-Noncoherent-Large-ω-Precategory)

open is-coinductive-iso-Noncoherent-Large-ω-Precategory public
```

### Coinductive isomorphisms in a noncoherent large ω-precategory

```agda
coinductive-iso-Noncoherent-Large-ω-Precategory :
  {α : Level → Level} {β : Level → Level → Level}
  (𝒞 : Noncoherent-Large-ω-Precategory α β)
  {l1 : Level} (x : obj-Noncoherent-Large-ω-Precategory 𝒞 l1)
  {l2 : Level} (y : obj-Noncoherent-Large-ω-Precategory 𝒞 l2) →
  UU (β l1 l1 ⊔ β l1 l2 ⊔ β l2 l1 ⊔ β l2 l2)
coinductive-iso-Noncoherent-Large-ω-Precategory 𝒞 x y =
  Σ ( hom-Noncoherent-Large-ω-Precategory 𝒞 x y)
    ( is-coinductive-iso-Noncoherent-Large-ω-Precategory 𝒞)
```

### Components of a coinductive isomorphism in a noncoherent large ω-precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {𝒞 : Noncoherent-Large-ω-Precategory α β}
  {l1 : Level} {x : obj-Noncoherent-Large-ω-Precategory 𝒞 l1}
  {l2 : Level} {y : obj-Noncoherent-Large-ω-Precategory 𝒞 l2}
  (f : coinductive-iso-Noncoherent-Large-ω-Precategory 𝒞 x y)
  where

  hom-coinductive-iso-Noncoherent-Large-ω-Precategory :
    hom-Noncoherent-Large-ω-Precategory 𝒞 x y
  hom-coinductive-iso-Noncoherent-Large-ω-Precategory = pr1 f

  is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory :
    is-coinductive-iso-Noncoherent-Large-ω-Precategory 𝒞
      ( hom-coinductive-iso-Noncoherent-Large-ω-Precategory)
  is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory = pr2 f

  hom-section-coinductive-iso-Noncoherent-Large-ω-Precategory :
    hom-Noncoherent-Large-ω-Precategory 𝒞 y x
  hom-section-coinductive-iso-Noncoherent-Large-ω-Precategory =
    hom-section-is-coinductive-iso-Noncoherent-Large-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory)

  unit-coinductive-iso-Noncoherent-Large-ω-Precategory :
    2-hom-Noncoherent-Large-ω-Precategory 𝒞
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-coinductive-iso-Noncoherent-Large-ω-Precategory)
        ( hom-section-coinductive-iso-Noncoherent-Large-ω-Precategory))
  unit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    unit-is-coinductive-iso-Noncoherent-Large-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory)

  is-coinductive-iso-unit-coinductive-iso-Noncoherent-Large-ω-Precategory :
    is-coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( unit-coinductive-iso-Noncoherent-Large-ω-Precategory)
  is-coinductive-iso-unit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    is-coinductive-iso-unit-is-coinductive-iso-Noncoherent-Large-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory)

  coinductive-iso-unit-coinductive-iso-Noncoherent-Large-ω-Precategory :
    coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-coinductive-iso-Noncoherent-Large-ω-Precategory)
        ( hom-section-coinductive-iso-Noncoherent-Large-ω-Precategory))
  pr1 coinductive-iso-unit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    unit-coinductive-iso-Noncoherent-Large-ω-Precategory
  pr2 coinductive-iso-unit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    is-coinductive-iso-unit-coinductive-iso-Noncoherent-Large-ω-Precategory

  hom-retraction-coinductive-iso-Noncoherent-Large-ω-Precategory :
    hom-Noncoherent-Large-ω-Precategory 𝒞 y x
  hom-retraction-coinductive-iso-Noncoherent-Large-ω-Precategory =
    hom-retraction-is-coinductive-iso-Noncoherent-Large-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory)

  counit-coinductive-iso-Noncoherent-Large-ω-Precategory :
    2-hom-Noncoherent-Large-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-retraction-coinductive-iso-Noncoherent-Large-ω-Precategory)
        ( hom-coinductive-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  counit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    counit-is-coinductive-iso-Noncoherent-Large-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory)

  is-coinductive-iso-counit-coinductive-iso-Noncoherent-Large-ω-Precategory :
    is-coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( counit-coinductive-iso-Noncoherent-Large-ω-Precategory)
  is-coinductive-iso-counit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    is-coinductive-iso-counit-is-coinductive-iso-Noncoherent-Large-ω-Precategory
      ( is-coinductive-iso-hom-coinductive-iso-Noncoherent-Large-ω-Precategory)

  coinductive-iso-counit-coinductive-iso-Noncoherent-Large-ω-Precategory :
    coinductive-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-retraction-coinductive-iso-Noncoherent-Large-ω-Precategory)
        ( hom-coinductive-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  pr1 coinductive-iso-counit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    counit-coinductive-iso-Noncoherent-Large-ω-Precategory
  pr2 coinductive-iso-counit-coinductive-iso-Noncoherent-Large-ω-Precategory =
    is-coinductive-iso-counit-coinductive-iso-Noncoherent-Large-ω-Precategory
```

## See also

- [Coinductive isomorphisms in noncoherent ω-precategories](wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories.md)

## References

{{#bibliography}}
