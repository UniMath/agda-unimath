# Coequalizers

```agda
module synthetic-homotopy-theory.coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.double-arrows
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

The
{{#concept "coequalizer" Disambiguation="of a double arrow of types" WDID=Q5140810 WD="coequalizer"}}
of a [double arrow](foundation.double-arrows.md) `f, g : A → B` is the
colimiting [cofork](synthetic-homotopy-theory.coforks.md), i.e., a cofork with
the
[universal property of coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md).

## Properties

### All double arrows admit a coequalizer

The
{{#concept "standard coequalizer" Disambiguation="of types" Agda=standard-coequalizer}}
is obtained as a [pushout](synthetic-homotopy-theory.pushouts.md) of the span

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
  {l1 l2 : Level} (a : double-arrow l1 l2)
  where

  abstract
    standard-coequalizer : UU (l1 ⊔ l2)
    standard-coequalizer =
      pushout
        ( vertical-map-span-cocone-cofork a)
        ( horizontal-map-span-cocone-cofork a)

    cofork-standard-coequalizer : cofork a standard-coequalizer
    cofork-standard-coequalizer =
      cofork-cocone-codiagonal a
        ( cocone-pushout
          ( vertical-map-span-cocone-cofork a)
          ( horizontal-map-span-cocone-cofork a))

    dup-standard-coequalizer :
      dependent-universal-property-coequalizer a cofork-standard-coequalizer
    dup-standard-coequalizer =
      dependent-universal-property-coequalizer-dependent-universal-property-pushout
        ( a)
        ( cofork-standard-coequalizer)
        ( λ P →
          tr
            ( λ c →
              is-equiv
                ( dependent-cocone-map
                  ( vertical-map-span-cocone-cofork a)
                  ( horizontal-map-span-cocone-cofork a)
                  ( c)
                  ( P)))
            ( inv
              ( is-retraction-map-inv-is-equiv
                ( is-equiv-cofork-cocone-codiagonal a)
                ( cocone-pushout
                  ( vertical-map-span-cocone-cofork a)
                  ( horizontal-map-span-cocone-cofork a))))
            ( dup-pushout
              ( vertical-map-span-cocone-cofork a)
              ( horizontal-map-span-cocone-cofork a)
              ( P)))

    up-standard-coequalizer :
      universal-property-coequalizer a cofork-standard-coequalizer
    up-standard-coequalizer =
      universal-property-dependent-universal-property-coequalizer a
        ( cofork-standard-coequalizer)
        ( dup-standard-coequalizer)
```
