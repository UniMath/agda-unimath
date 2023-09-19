# Coequalizers

```agda
module synthetic-homotopy-theory.coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.codiagonal-maps-of-types
open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-coforks
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

The **canonical coequalizer** may be obtained as a pushout of the span

```text
     ∇         [f,g]
A <----- A + A -----> B
```

where the left map is the codiagonal map, sending `inl(a)` and `inr(a)` to `a`,
and the right map is defined by the universal property of coproducts to send
`inl(a)` to `f(a)` and `inr(a)` to `g(a)`.

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
      pushout (∇ A) (ind-coprod (λ _ → B) f g)

    cofork-canonical-coequalizer : cofork f g canonical-coequalizer
    cofork-canonical-coequalizer =
      cofork-cocone-codiagonal f g
        ( cocone-pushout (∇ A) (ind-coprod (λ _ → B) f g))

    dup-canonical-coequalizer :
      { l : Level} →
      dependent-universal-property-coequalizer l f g
        ( cofork-canonical-coequalizer)
    dup-canonical-coequalizer P =
      is-equiv-comp-htpy
        ( dependent-cofork-map f g cofork-canonical-coequalizer)
        ( dependent-cofork-dependent-cocone-codiagonal f g
          ( cofork-canonical-coequalizer)
          ( P))
        ( dependent-cocone-map
          ( ∇ A)
          ( ind-coprod (λ _ → B) f g)
          ( cocone-codiagonal-cofork f g cofork-canonical-coequalizer)
          ( P))
        ( triangle-dependent-cofork-dependent-cocone-codiagonal f g
          ( cofork-canonical-coequalizer)
          ( P))
        ( tr
          ( λ c →
            is-equiv
              ( dependent-cocone-map
                ( ∇ A)
                ( ind-coprod (λ _ → B) f g)
                ( c)
                ( P)))
          ( inv
            ( is-retraction-map-inv-is-equiv
              ( is-equiv-cofork-cocone-codiagonal f g)
              ( cocone-pushout (∇ A) (ind-coprod (λ _ → B) f g))))
          ( dependent-up-pushout
            ( ∇ A)
            ( ind-coprod (λ _ → B) f g)
            ( P)))
        ( is-equiv-dependent-cofork-dependent-cocone-codiagonal f g
          ( cofork-canonical-coequalizer)
          ( P))

    up-canonical-coequalizer :
      { l : Level} →
      universal-property-coequalizer l f g cofork-canonical-coequalizer
    up-canonical-coequalizer =
      universal-property-dependent-universal-property-coequalizer f g
        ( cofork-canonical-coequalizer)
        ( dup-canonical-coequalizer)
```
