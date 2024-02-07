# Fibers of cogap maps of pushouts

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module synthetic-homotopy-theory.fibers-of-cogap-maps-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

### Computing the fibers of the cogap map

We characterize the [fibers](foundation-core.fibers-of-maps.md) of the cogap map
as a pushout of fibers. This is an application of the
[flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md).

Given a pushout 𝒮quare with a
[cocone](synthetic-homotopy-theory.cocones-under-span-diagrams.md)

```text
       g
   S -------> B
   |          | \
 f |       inr|  \  n
   v  inl   ⌜ v   \
   A -------> ∙    \
    \          \   |
  m  \    cogap \  |
      \          ∨ v
        --------> X
```

we have, for every `x : X`, a pushout 𝒮quare of fibers:

```text
    fiber (m ∘ f) x ---> fiber (cogap ∘ inr) x
           |                       |
           |                       |
           v                     ⌜ v
 fiber (cogap ∘ inl) x ----> fiber cogap x
```

```agda
module _
  { l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram 𝒮 X) (x : X)
  where

  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span :
    fiber (left-map-cocone-span-diagram 𝒮 c ∘ left-map-span-diagram 𝒮) x ≃
    fiber
      ( cogap-cocone-span-diagram 𝒮 c ∘
        inl-standard-pushout 𝒮 ∘
        left-map-span-diagram 𝒮)
      ( x)
  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span =
    equiv-tot
      ( λ y →
        equiv-concat
          ( compute-inl-cogap-cocone-span-diagram 𝒮 c
            ( left-map-span-diagram 𝒮 y))
          ( x))

  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl :
    fiber (left-map-cocone-span-diagram 𝒮 c) x ≃
    fiber (cogap-cocone-span-diagram 𝒮 c ∘ inl-standard-pushout 𝒮) x
  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl =
    equiv-tot
      ( λ a → equiv-concat (compute-inl-cogap-cocone-span-diagram 𝒮 c a) x)

  equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr :
    fiber (right-map-cocone-span-diagram 𝒮 c) x ≃
    fiber (cogap-cocone-span-diagram 𝒮 c ∘ inr-standard-pushout 𝒮) x
  equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr =
    equiv-tot
      ( λ b → equiv-concat (compute-inr-cogap-cocone-span-diagram 𝒮 c b) x)

  left-map-span-cogap-cocone-span-diagram-fiber :
    fiber (left-map-cocone-span-diagram 𝒮 c ∘ left-map-span-diagram 𝒮) x →
    fiber (left-map-cocone-span-diagram 𝒮 c) x
  left-map-span-cogap-cocone-span-diagram-fiber =
    map-Σ-map-base
      ( left-map-span-diagram 𝒮)
      ( λ a → left-map-cocone-span-diagram 𝒮 c a ＝ x)

  right-map-span-cogap-cocone-span-diagram-fiber :
    fiber (left-map-cocone-span-diagram 𝒮 c ∘ left-map-span-diagram 𝒮) x →
    fiber (right-map-cocone-span-diagram 𝒮 c) x
  right-map-span-cogap-cocone-span-diagram-fiber =
    ( map-inv-equiv
      equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr) ∘
    {!!}
    {-
    ( left-map-flattening-pushout
      s -- ( transposition-span-diagram 𝒮)
      ( cocone-standard-pushout 𝒮)
      -- ( cocone-standard-pushout (transposition-span-diagram 𝒮))
      {! λ y → (cogap-cocone-span-diagram 𝒮 c y) ＝ x!})
    {-
      ( left-map-flattening-pushout
        ( λ y → (cogap-cocone-span-diagram 𝒮 c y) ＝ x)
        s
        cocone-standard-pushout) -} -} ∘
    ( map-equiv
      equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span)
```

Since our pushout 𝒮quare of fibers has `fiber (m ∘ f) x` as its top-left corner
and not `fiber (n ∘ g) x`, things are "left-biased". For this reason, the
following map is constructed as a composition which makes a later coherence
square commute (almost) trivially.

```text
  statement-universal-property-pushout-cogap-cocone-span-diagram-fiber : UUω
  statement-universal-property-pushout-cogap-cocone-span-diagram-fiber =
    { l : Level} →
    Σ ( cocone-span-diagram
        ( left-map-span-cogap-cocone-span-diagram-fiber)
        ( right-map-span-cogap-cocone-span-diagram-fiber)
        ( fiber (cogap-cocone-span-diagram 𝒮 c) x))
      ( universal-property-pushout l
        ( left-map-span-cogap-cocone-span-diagram-fiber)
        ( right-map-span-cogap-cocone-span-diagram-fiber))

  universal-property-pushout-cogap-cocone-span-diagram-fiber :
    statement-universal-property-pushout-cogap-cocone-span-diagram-fiber
  universal-property-pushout-cogap-cocone-span-diagram-fiber = ?

{-
    universal-property-pushout-extension-by-equivalences
      ( right-map-span-flattening-pushout
        ( λ y → cogap-cocone-span-diagram f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-standard-pushout f g))
      ( left-map-span-flattening-pushout
        ( λ y → cogap-cocone-span-diagram f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-standard-pushout f g))
      ( left-map-span-cogap-cocone-span-diagram-fiber)
      ( right-map-span-cogap-cocone-span-diagram-fiber)
      ( map-equiv
        equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl)
      ( map-equiv
        equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr)
      ( map-equiv
        equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span)
      ( cocone-flattening-pushout
        ( λ y → cogap-cocone-span-diagram f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-standard-pushout f g))
      ( flattening-lemma-pushout
        ( λ y → cogap-cocone-span-diagram f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-standard-pushout f g)
        ( dependent-universal-property-pushout f g))
      ( refl-htpy)
      ( λ _ →
        inv
          ( is-section-map-inv-equiv
            ( equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr)
            ( _)))
      ( is-equiv-map-equiv
        equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl)
      ( is-equiv-map-equiv
        equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr)
      ( is-equiv-map-equiv
        ( equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span)) -}
```

We record the following auxiliary lemma which says that if we have types `T`,
`F` and `G` such that `T ≃ fiber (m ∘ f) x`, `F ≃ fiber (cogap ∘ inl) x` and
`G ≃ fiber (cogap ∘ inr) x`, together with suitable maps `u : T → F` and
`v : T → G`, then we get a pushout 𝒮quare:

```text
          v
   T ----------> G
   |             |
 u |             |
   v           ⌜ v
   F ----> fiber cogap x
```

Thus, this lemma is useful in case we have convenient descriptions of the
fibers.

```text
  module _
    { l5 l6 l7 : Level} (T : UU l5) (F : UU l6) (G : UU l7)
    ( i : F ≃ fiber (left-map-cocone-span-diagram 𝒮 c) x)
    ( j : G ≃ fiber (right-map-cocone-span-diagram 𝒮 c) x)
    ( k :
      T ≃ fiber (left-map-cocone-span-diagram 𝒮 c ∘ left-map-span-diagram 𝒮) x)
    ( u : T → F)
    ( v : T → G)
    ( coh-l :
      coherence-square-maps
        ( map-equiv k)
        ( u)
        ( left-map-span-cogap-cocone-span-diagram-fiber)
        ( map-equiv i))
    ( coh-r :
      coherence-square-maps
        ( v)
        ( map-equiv k)
        ( map-equiv j)
        ( right-map-span-cogap-cocone-span-diagram-fiber))
    where

    universal-property-pushout-cogap-cocone-span-diagram-fiber-universal-property-to-equiv :
      { l : Level} →
      ( Σ ( cocone-span-diagram u v (fiber (cogap-cocone-span-diagram 𝒮 c) x))
          ( λ c → universal-property-pushout l u v c))
    universal-property-pushout-cogap-cocone-span-diagram-fiber-universal-property-to-equiv
      {l} =
      universal-property-pushout-comp-cocone-equiv-span-diagram
        ( left-map-span-cogap-cocone-span-diagram-fiber)
        ( right-map-span-cogap-cocone-span-diagram-fiber)
        ( u)
        ( v)
        ( map-equiv i)
        ( map-equiv j)
        ( map-equiv k)
        ( pr1 (universal-property-pushout-cogap-cocone-span-diagram-fiber {l}))
        ( pr2 universal-property-pushout-cogap-cocone-span-diagram-fiber)
        ( coh-l)
        ( coh-r)
        ( is-equiv-map-equiv i)
        ( is-equiv-map-equiv j)
        ( is-equiv-map-equiv k)
```

