# Coequalizers

```agda
module synthetic-homotopy-theory.coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.codiagonal-maps-of-types
open import foundation.commuting-triangles-of-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

The **coequalizer** of a parallel pair `f, g : A → B` is the colimiting
[cofork](synthetic-homotopy-theory.coforks.md), i.e. a cofork with the
[universal property of coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md).

## Definitions

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

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B)
  where

  cofork-cocone-codiagonal :
    { l3 : Level} {X : UU l3} →
    cocone (∇ A) (ind-coprod (λ _ → B) f g) X →
    cofork f g X
  pr1 (cofork-cocone-codiagonal c) =
    vertical-map-cocone (∇ A) (ind-coprod (λ _ → B) f g) c
  pr2 (cofork-cocone-codiagonal c) =
      ( ( inv-htpy
          ( coherence-square-cocone (∇ A) (ind-coprod (λ _ → B) f g) c)) ·r
        ( inl)) ∙h
      ( ( coherence-square-cocone (∇ A) (ind-coprod (λ _ → B) f g) c) ·r inr)

  cocone-codiagonal-cofork :
    { l3 : Level} {X : UU l3} →
    cofork f g X →
    cocone (∇ A) (ind-coprod (λ _ → B) f g) X
  pr1 (cocone-codiagonal-cofork e) = map-cofork f g e ∘ f
  pr1 (pr2 (cocone-codiagonal-cofork e)) = map-cofork f g e
  pr2 (pr2 (cocone-codiagonal-cofork e)) (inl a) = refl
  pr2 (pr2 (cocone-codiagonal-cofork e)) (inr a) = coherence-cofork f g e a

  is-equiv-cofork-cocone-codiagonal :
    { l3 : Level} {X : UU l3} →
    is-equiv (cofork-cocone-codiagonal {X = X})
  is-equiv-cofork-cocone-codiagonal =
    is-equiv-is-invertible
      cocone-codiagonal-cofork
        ( λ e →
          eq-htpy-cofork f g
            ( cofork-cocone-codiagonal (cocone-codiagonal-cofork e))
            ( e)
            ( refl-htpy , right-unit-htpy))
        ( λ c →
          eq-htpy-cocone
            ( ∇ A)
            ( ind-coprod (λ _ → B) f g)
            ( cocone-codiagonal-cofork (cofork-cocone-codiagonal c))
            ( c)
            ( ( ( inv-htpy
                  ( coherence-square-cocone
                    ( ∇ A)
                    ( ind-coprod (λ _ → B) f g)
                    ( c))) ·r
                ( inl)) ,
              ( refl-htpy) ,
              ( λ { (inl a) →
                    inv
                      ( left-inv
                        ( coherence-square-cocone
                          ( ∇ A)
                          ( ind-coprod (λ _ → B) f g)
                          ( c)
                          ( inl a)))
                  ; (inr a) → right-unit })))

  triangle-cofork-cocone :
    { l3 l4 : Level} {X : UU l3} {Y : UU l4} →
    ( c : cocone (∇ A) (ind-coprod (λ _ → B) f g) X) →
    coherence-triangle-maps
      ( cofork-map f g (cofork-cocone-codiagonal c) {Y = Y})
      ( cofork-cocone-codiagonal)
      ( cocone-map (∇ A) (ind-coprod (λ _ → B) f g) c)
  triangle-cofork-cocone c h =
    eq-htpy-cofork f g
      ( cofork-map f g (cofork-cocone-codiagonal c) h)
      ( cofork-cocone-codiagonal
        ( cocone-map (∇ A) (ind-coprod (λ _ → B) f g) c h))
      ( refl-htpy ,
        ( right-unit-htpy ∙h
          ( λ a →
            ( ap-concat h
              ( inv
                ( coherence-square-cocone
                  ( ∇ A)
                  ( ind-coprod (λ _ → B) f g)
                  ( c)
                  ( inl a)))
              ( coherence-square-cocone
                ( ∇ A)
                ( ind-coprod (λ _ → B) f g)
                ( c)
                ( inr a))) ∙
            ( identification-right-whisk
              ( ap-inv h
                ( coherence-square-cocone
                  ( ∇ A)
                  ( ind-coprod (λ _ → B) f g)
                  ( c)
                  ( inl a)))
              ( ap h
                ( coherence-square-cocone
                  ( ∇ A)
                  ( ind-coprod (λ _ → B) f g)
                  ( c)
                  ( inr a)))))))

  abstract
    canonical-coequalizer : UU (l1 ⊔ l2)
    canonical-coequalizer =
      pushout (∇ A) (ind-coprod (λ _ → B) f g)

    cofork-canonical-coequalizer : cofork f g canonical-coequalizer
    cofork-canonical-coequalizer =
      cofork-cocone-codiagonal
        ( cocone-pushout (∇ A) (ind-coprod (λ _ → B) f g))

    up-canonical-coequalizer :
      { l : Level} →
      universal-property-coequalizer l f g cofork-canonical-coequalizer
    up-canonical-coequalizer Y =
      is-equiv-comp-htpy
        ( cofork-map f g cofork-canonical-coequalizer)
        ( cofork-cocone-codiagonal)
        ( cocone-map
          ( ∇ A)
          ( ind-coprod (λ _ → B) f g)
          ( cocone-pushout (∇ A) (ind-coprod (λ _ → B) f g)))
        ( triangle-cofork-cocone
          ( cocone-pushout (∇ A) (ind-coprod (λ _ → B) f g)))
        ( up-pushout (∇ A) (ind-coprod (λ _ → B) f g) Y)
        ( is-equiv-cofork-cocone-codiagonal)
```
