# Coequalizers

```agda
{-# OPTIONS --cubical-compatible #-}

module synthetic-homotopy-theory.coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-coequalizers
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

The **coequalizer** of a parallel pair `f, g : A → B` is the colimiting
[cofork](synthetic-homotopy-theory.coforks.md), i.e. a cofork with the
[universal property of coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md).

## Properties

### All parallel pairs admit a coequalizer

The **canonical coequalizer** may be obtained as a
[pushout](synthetic-homotopy-theory.pushouts.md) of the span

```text
     ∇         [f,g]
A <----- A + A -----> B
```

where the left map is the
[codiagonal map](foundation.codiagonal-maps-of-types.md), sending `inl(a)` and
`inr(a)` to `a`, and the right map is defined by the universal property of
[coproducts](foundation.coproduct-types.md) to send `inl(a)` to `f(a)` and
`inr(a)` to `g(a)`.

The pushout thus constructed will consist of a copy of `B`, a copy of `A`, and
for every point `a` of `A` there will be a path from `f(a)` to `a` and to
`g(a)`, which corresponds to having a copy of `B` with paths connecting every
`f(a)` to `g(a)`.

The construction from pushouts itself is an implementation detail, which is why
the definition is marked abstract.

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  abstract
    canonical-coequalizer : UU (l1 ⊔ l2)
    canonical-coequalizer =
      pushout
        ( vertical-map-span-cocone-cofork f g)
        ( horizontal-map-span-cocone-cofork f g)

    cofork-canonical-coequalizer : cofork f g canonical-coequalizer
    cofork-canonical-coequalizer =
      cofork-cocone-codiagonal f g
        ( cocone-pushout
          ( vertical-map-span-cocone-cofork f g)
          ( horizontal-map-span-cocone-cofork f g))

    dup-canonical-coequalizer :
      { l : Level} →
      dependent-universal-property-coequalizer l f g
        ( cofork-canonical-coequalizer)
    dup-canonical-coequalizer =
      dependent-universal-property-coequalizer-dependent-universal-property-pushout
        ( f)
        ( g)
        ( cofork-canonical-coequalizer)
        ( λ P →
          tr
            ( λ c →
              is-equiv
                ( dependent-cocone-map
                  ( vertical-map-span-cocone-cofork f g)
                  ( horizontal-map-span-cocone-cofork f g)
                  ( c)
                  ( P)))
            ( inv
              ( is-retraction-map-inv-is-equiv
                ( is-equiv-cofork-cocone-codiagonal f g)
                ( cocone-pushout
                  ( vertical-map-span-cocone-cofork f g)
                  ( horizontal-map-span-cocone-cofork f g))))
            ( dependent-up-pushout
              ( vertical-map-span-cocone-cofork f g)
              ( horizontal-map-span-cocone-cofork f g)
              ( P)))

    up-canonical-coequalizer :
      { l : Level} →
      universal-property-coequalizer l f g cofork-canonical-coequalizer
    up-canonical-coequalizer =
      universal-property-dependent-universal-property-coequalizer f g
        ( cofork-canonical-coequalizer)
        ( dup-canonical-coequalizer)
```
