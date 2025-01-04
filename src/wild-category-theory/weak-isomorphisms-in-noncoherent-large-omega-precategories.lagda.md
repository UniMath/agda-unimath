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

- a morphism `s : 𝒞₁ y x`
- a $2$-morphism `η : 𝒞₂ id (f ∘ s)`
- a witness that `η` is itself a weak isomorphism
- another morphism `r : 𝒞₁ y x`
- a $2$-morphism `ε : 𝒞₂ (r ∘ f) id`
- a witness that `ε` is a weak isomorphism.

Thus, the specified data is a commuting diagram of the form

```text
  y ========= y
    \  ~⇓η  ∧   \
   s \     /f    \ r
      ∨   /  ~⇓ε  ∨
        x ========= x
```

where `η` and `ε` again are weak isomorphisms in their respective
hom-ω-categories.

> **Disclaimer.** It is not established that the proposed structure of a weak
> isomorphism is fully coherent, and may be subject to change in the future.

While a noncoherent ω-precategory is the most general setting that allows us to
_define_ weak isomorphisms, the missing coherences obstruct us from showing many
of the expected properties. For example, we cannot show that all identities are
weak isomorphisms or that weak isomorphisms compose.

The concept of weak isomorphisms in ω-categories is strictly weaker than the
concept of _isomorphisms_. Indeed, the coindutive nature of this concept allows
us, in an informal sense, to postpone providing a witness that `s` or `r` are
"proper" inverses to `f` all the way up to infinity. To take an example,
consider the ω-category of spans and higher spans. In this ω-category every
morphism is a weak isomorphism since every morphism is a biadjoint, but not
every morphism is an isomorphism. Moreover, this ω-category is univalent with
respect to isomorphisms, but not with respect to all weak isomorphisms.

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

    unit-is-weak-iso-Noncoherent-Large-ω-Precategory :
      2-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
          ( f)
          ( hom-section-is-weak-iso-Noncoherent-Large-ω-Precategory))

    is-weak-iso-unit-is-weak-iso-Noncoherent-Large-ω-Precategory :
      is-weak-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
          ( 𝒞)
          ( y)
          ( y))
        ( unit-is-weak-iso-Noncoherent-Large-ω-Precategory)

    hom-retraction-is-weak-iso-Noncoherent-Large-ω-Precategory :
      hom-Noncoherent-Large-ω-Precategory 𝒞 y x

    counit-is-weak-iso-Noncoherent-Large-ω-Precategory :
      2-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
          ( hom-retraction-is-weak-iso-Noncoherent-Large-ω-Precategory)
          ( f))
        ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)

    is-weak-iso-counit-is-weak-iso-Noncoherent-Large-ω-Precategory :
      is-weak-iso-Noncoherent-ω-Precategory
        ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
          ( 𝒞)
          ( x)
          ( x))
        ( counit-is-weak-iso-Noncoherent-Large-ω-Precategory)

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

  unit-weak-iso-Noncoherent-Large-ω-Precategory :
    2-hom-Noncoherent-Large-ω-Precategory 𝒞
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-section-weak-iso-Noncoherent-Large-ω-Precategory))
  unit-weak-iso-Noncoherent-Large-ω-Precategory =
    unit-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  is-weak-iso-unit-weak-iso-Noncoherent-Large-ω-Precategory :
    is-weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( unit-weak-iso-Noncoherent-Large-ω-Precategory)
  is-weak-iso-unit-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-unit-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  weak-iso-unit-weak-iso-Noncoherent-Large-ω-Precategory :
    weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( y)
        ( y))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-section-weak-iso-Noncoherent-Large-ω-Precategory))
  pr1 weak-iso-unit-weak-iso-Noncoherent-Large-ω-Precategory =
    unit-weak-iso-Noncoherent-Large-ω-Precategory
  pr2 weak-iso-unit-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-unit-weak-iso-Noncoherent-Large-ω-Precategory

  hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory :
    hom-Noncoherent-Large-ω-Precategory 𝒞 y x
  hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory =
    hom-retraction-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  counit-weak-iso-Noncoherent-Large-ω-Precategory :
    2-hom-Noncoherent-Large-ω-Precategory 𝒞
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  counit-weak-iso-Noncoherent-Large-ω-Precategory =
    counit-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  is-weak-iso-counit-weak-iso-Noncoherent-Large-ω-Precategory :
    is-weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( counit-weak-iso-Noncoherent-Large-ω-Precategory)
  is-weak-iso-counit-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-counit-is-weak-iso-Noncoherent-Large-ω-Precategory
      ( is-weak-iso-hom-weak-iso-Noncoherent-Large-ω-Precategory)

  weak-iso-counit-weak-iso-Noncoherent-Large-ω-Precategory :
    weak-iso-Noncoherent-ω-Precategory
      ( hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
        ( 𝒞)
        ( x)
        ( x))
      ( comp-hom-Noncoherent-Large-ω-Precategory 𝒞
        ( hom-retraction-weak-iso-Noncoherent-Large-ω-Precategory)
        ( hom-weak-iso-Noncoherent-Large-ω-Precategory))
      ( id-hom-Noncoherent-Large-ω-Precategory 𝒞)
  pr1 weak-iso-counit-weak-iso-Noncoherent-Large-ω-Precategory =
    counit-weak-iso-Noncoherent-Large-ω-Precategory
  pr2 weak-iso-counit-weak-iso-Noncoherent-Large-ω-Precategory =
    is-weak-iso-counit-weak-iso-Noncoherent-Large-ω-Precategory
```

## See also

- [Weak isomorphisms in noncoherent ω-precategories](wild-category-theory.weak-isomorphisms-in-noncoherent-omega-precategories.md)
