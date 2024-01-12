# Pushouts

```agda
module synthetic-homotopy-theory.pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.transposition-span-diagrams
open import foundation.universe-levels

open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` of types

```text
      f     g
  A <--- S ---> B.
```

The {{#concept "standard pushout"}} `A ⊔_𝒮 B` of `𝒮` is a postulated choice of a type `X` equipped with a
[cocone structure](synthetic-homotopy-theory.cocones-under-span-diagrams.md) of
`𝒮` with codomain `X` satisfying the
[universal property of the pushout](synthetic-homotopy-theory.universal-property-pushouts.md)
of `𝒮`. In other words, the standard pushout `A ⊔_𝒮 B` of `𝒮` comes equipped with a cocone
structure `(inl , inr , glue)` where

```text
          g
    S --------> B
    |           |
  f |   glue    | inr
    V           V
    A ------> A ⊔_𝒮 B,
        inl
```

such that for any type `Y`, the [evaluation map](synthetic-homotopy-theory.operations-cocones-under-span-diagrams.md)

```text
  (A ⊔_𝒮 B → Y) → cocone 𝒮 Y
```

is an [equivalence](foundation-core.equivalences.md).

## Postulates

We will assume that for any span diagram

```text
      f     g
  A <--- S ---> B,
```

where `S : UU l1`, `A : UU l2`, and `B : UU l3` there is a pushout in
`UU (l1 ⊔ l2 ⊔ l3)`.

```agda
module _
  {l1 l2 l3 : Level} (s : span-diagram l1 l2 l3)
  where
  
  postulate
    standard-pushout : UU (l1 ⊔ l2 ⊔ l3)

  postulate
    inl-standard-pushout : domain-span-diagram s → standard-pushout

  postulate
    inr-standard-pushout : codomain-span-diagram s → standard-pushout

  postulate
    glue-standard-pushout :
      coherence-square-maps
        ( right-map-span-diagram s)
        ( left-map-span-diagram s)
        ( inr-standard-pushout)
        ( inl-standard-pushout)

  cocone-standard-pushout :
    cocone-span-diagram s standard-pushout
  pr1 cocone-standard-pushout = inl-standard-pushout
  pr1 (pr2 cocone-standard-pushout) = inr-standard-pushout
  pr2 (pr2 cocone-standard-pushout) = glue-standard-pushout

  postulate
    universal-property-pushout-standard-pushout :
      universal-property-pushout s cocone-standard-pushout

  equiv-universal-property-pushout-standard-pushout :
    {l4 : Level} (X : UU l4) → (standard-pushout → X) ≃ cocone-span-diagram s X
  pr1 (equiv-universal-property-pushout-standard-pushout X) =
    cocone-map-span-diagram s cocone-standard-pushout
  pr2 (equiv-universal-property-pushout-standard-pushout X) =
    universal-property-pushout-standard-pushout X
```

## Definitions

### The cogap map

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) {X : UU l4}
  where

  cogap-cocone-span-diagram : cocone-span-diagram s X → standard-pushout s → X
  cogap-cocone-span-diagram =
    map-inv-equiv (equiv-universal-property-pushout-standard-pushout s X)

  is-section-cogap-cocone-span-diagram :
    is-section
      ( cocone-map-span-diagram s (cocone-standard-pushout s))
      ( cogap-cocone-span-diagram)
  is-section-cogap-cocone-span-diagram =
    is-section-map-inv-equiv
      ( equiv-universal-property-pushout-standard-pushout s X)

  is-retraction-cogap-cocone-span-diagram :
    is-retraction
      ( cocone-map-span-diagram s (cocone-standard-pushout s))
      ( cogap-cocone-span-diagram)
  is-retraction-cogap-cocone-span-diagram =
    is-retraction-map-inv-equiv
      ( equiv-universal-property-pushout-standard-pushout s X)
```

### The predicate on cocones under span diagrams of being a pushout cocone

The `is-pushout` predicate defined below is a [small type](foundation.small-types.md), as opposed to the universal property of pushouts, which is in `UUω`.

```agda
is-pushout :
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) {X : UU l4}
  (c : cocone-span-diagram s X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-pushout s c = is-equiv (cogap-cocone-span-diagram s c)
```

## Properties

### Standard pushouts satisfy the universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  where

  universal-property-pushout-is-pushout :
    is-pushout s c → universal-property-pushout s c
  universal-property-pushout-is-pushout H =
    universal-property-pushout-universal-property-pushout-is-equiv s
      ( cocone-standard-pushout s)
      ( c)
      ( cogap-cocone-span-diagram s c)
      ( htpy-cocone-universal-property-pushout s
        ( cocone-standard-pushout s)
        ( universal-property-pushout-standard-pushout s)
        ( c))
      ( H)
      ( universal-property-pushout-standard-pushout s)

  is-pushout-universal-property-pushout :
    universal-property-pushout s c → is-pushout s c
  is-pushout-universal-property-pushout =
    is-equiv-universal-property-pushout-universal-property-pushout s
      ( cocone-standard-pushout s)
      ( c)
      ( cogap-cocone-span-diagram s c)
      ( htpy-cocone-universal-property-pushout s
        ( cocone-standard-pushout s)
        ( universal-property-pushout-standard-pushout s)
        ( c))
      ( universal-property-pushout-standard-pushout s)
```

### Standard pushouts satisfy the dependent universal property of pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  where

  dependent-universal-property-pushout-standard-pushout :
    dependent-universal-property-pushout s (cocone-standard-pushout s)
  dependent-universal-property-pushout-standard-pushout =
    dependent-universal-property-universal-property-pushout
      ( s)
      ( cocone-standard-pushout s)
      ( universal-property-pushout-standard-pushout s)

  equiv-dependent-universal-property-pushout :
    (P : standard-pushout s → UU l4) →
    ((x : standard-pushout s) → P x) ≃
    dependent-cocone-span-diagram s (cocone-standard-pushout s) P
  pr1 (equiv-dependent-universal-property-pushout P) =
    dependent-cocone-map-span-diagram s (cocone-standard-pushout s) P
  pr2 (equiv-dependent-universal-property-pushout P) =
    dependent-universal-property-pushout-standard-pushout P
```

### Computation with the cogap map

```agda
module _
  { l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram s X)
  where

  compute-inl-cogap-cocone-span-diagram :
    ( a : domain-span-diagram s) →
    cogap-cocone-span-diagram s c (inl-standard-pushout s a) ＝
    left-map-cocone-span-diagram s c a
  compute-inl-cogap-cocone-span-diagram =
    left-htpy-cocone-universal-property-pushout
      ( s)
      ( cocone-standard-pushout s)
      ( universal-property-pushout-standard-pushout s)
      ( c)

  compute-inr-cogap-cocone-span-diagram :
    ( b : codomain-span-diagram s) →
    cogap-cocone-span-diagram s c (inr-standard-pushout s b) ＝
    right-map-cocone-span-diagram s c b
  compute-inr-cogap-cocone-span-diagram =
    right-htpy-cocone-universal-property-pushout
      ( s)
      ( cocone-standard-pushout s)
      ( universal-property-pushout-standard-pushout s)
      ( c)

  compute-glue-cogap-cocone-span-diagram :
    statement-coherence-htpy-cocone-span-diagram s
      ( cocone-map-span-diagram s
        ( cocone-standard-pushout s)
        ( cogap-cocone-span-diagram s c))
      ( c)
      ( compute-inl-cogap-cocone-span-diagram)
      ( compute-inr-cogap-cocone-span-diagram)
  compute-glue-cogap-cocone-span-diagram =
    coherence-htpy-cocone-universal-property-pushout
      ( s)
      ( cocone-standard-pushout s)
      ( universal-property-pushout-standard-pushout s)
      ( c)
```

### Computing the fibers of the cogap map

We characterize the [fibers](foundation-core.fibers-of-maps.md) of the cogap map
as a pushout of fibers. This is an application of the
[flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md).

Given a pushout square with a
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

we have, for every `x : X`, a pushout square of fibers:

```text
    fiber (m ∘ f) x ---> fiber (cogap ∘ inr) x
           |                       |
           |                       |
           v                     ⌜ v
 fiber (cogap ∘ inl) x ----> fiber cogap x
```

```agda
module _
  { l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram s X) (x : X)
  where

  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span :
    fiber (left-map-cocone-span-diagram s c ∘ left-map-span-diagram s) x ≃
    fiber
      ( cogap-cocone-span-diagram s c ∘ inl-standard-pushout s ∘ left-map-span-diagram s)
      ( x)
  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span =
    equiv-tot
      ( λ y →
        equiv-concat
          ( compute-inl-cogap-cocone-span-diagram s c
            ( left-map-span-diagram s y))
          ( x))

  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl :
    fiber (left-map-cocone-span-diagram s c) x ≃
    fiber (cogap-cocone-span-diagram s c ∘ inl-standard-pushout s) x
  equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl =
    equiv-tot
      ( λ a → equiv-concat (compute-inl-cogap-cocone-span-diagram s c a) x)

  equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr :
    fiber (right-map-cocone-span-diagram s c) x ≃
    fiber (cogap-cocone-span-diagram s c ∘ inr-standard-pushout s) x
  equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr =
    equiv-tot
      ( λ b → equiv-concat (compute-inr-cogap-cocone-span-diagram s c b) x)

  left-map-span-cogap-cocone-span-diagram-fiber :
    fiber (left-map-cocone-span-diagram s c ∘ left-map-span-diagram s) x →
    fiber (left-map-cocone-span-diagram s c) x
  left-map-span-cogap-cocone-span-diagram-fiber =
    map-Σ-map-base
      ( left-map-span-diagram s)
      ( λ a → left-map-cocone-span-diagram s c a ＝ x)

  right-map-span-cogap-cocone-span-diagram-fiber :
    fiber (left-map-cocone-span-diagram s c ∘ left-map-span-diagram s) x →
    fiber (right-map-cocone-span-diagram s c) x
  right-map-span-cogap-cocone-span-diagram-fiber =
    ( map-inv-equiv equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr) ∘
    {!!}
    {-
    ( left-map-flattening-pushout
      s -- ( transposition-span-diagram s)
      ( cocone-standard-pushout s) -- ( cocone-standard-pushout (transposition-span-diagram s))
      {! λ y → (cogap-cocone-span-diagram s c y) ＝ x!}) {- ( left-map-flattening-pushout
      ( λ y → (cogap-cocone-span-diagram s c y) ＝ x) s cocone-standard-pushout) -} -} ∘
    ( map-equiv equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span)
```

Since our pushout square of fibers has `fiber (m ∘ f) x` as its top-left corner
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
        ( fiber (cogap-cocone-span-diagram s c) x))
      ( universal-property-pushout l
        ( left-map-span-cogap-cocone-span-diagram-fiber)
        ( right-map-span-cogap-cocone-span-diagram-fiber))

  universal-property-pushout-cogap-cocone-span-diagram-fiber :
    statement-universal-property-pushout-cogap-cocone-span-diagram-fiber
  universal-property-pushout-cogap-cocone-span-diagram-fiber =
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
      ( map-equiv equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl)
      ( map-equiv equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr)
      ( map-equiv equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span)
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
      ( is-equiv-map-equiv equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl)
      ( is-equiv-map-equiv equiv-fiber-right-map-cocone-span-diagram-cogap-cocone-span-diagram-inr)
      ( is-equiv-map-equiv
        ( equiv-fiber-left-map-cocone-span-diagram-cogap-cocone-span-diagram-inl-horizontal-span))
```

We record the following auxiliary lemma which says that if we have types `T`,
`F` and `G` such that `T ≃ fiber (m ∘ f) x`, `F ≃ fiber (cogap ∘ inl) x` and
`G ≃ fiber (cogap ∘ inr) x`, together with suitable maps `u : T → F` and
`v : T → G`, then we get a pushout square:

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
    ( i : F ≃ fiber (left-map-cocone-span-diagram s c) x)
    ( j : G ≃ fiber (right-map-cocone-span-diagram s c) x)
    ( k : T ≃ fiber (left-map-cocone-span-diagram s c ∘ left-map-span-diagram s) x)
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
      ( Σ ( cocone-span-diagram u v (fiber (cogap-cocone-span-diagram s c) x))
          ( λ c → universal-property-pushout l u v c))
    universal-property-pushout-cogap-cocone-span-diagram-fiber-universal-property-to-equiv {l} =
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

### Swapping a pushout cocone yields another pushout cocone

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  (X : UU l4) (c : cocone-span-diagram s X)
  where

  universal-property-pushout-transposition-cocone-span-diagram-universal-property-pushout :
    universal-property-pushout s c →
    universal-property-pushout (transposition-span-diagram s) (transposition-cocone-span-diagram s c)
  universal-property-pushout-transposition-cocone-span-diagram-universal-property-pushout up Y =
    is-equiv-equiv'
      ( id-equiv)
      ( equiv-transposition-cocone-span-diagram s Y)
      ( λ h →
        eq-htpy-cocone-span-diagram
          ( transposition-span-diagram s)
          ( transposition-cocone-span-diagram s
            ( cocone-map-span-diagram s c h))
          ( cocone-map-span-diagram
            ( transposition-span-diagram s)
            ( transposition-cocone-span-diagram s c)
            ( h))
          ( ( refl-htpy) ,
            ( refl-htpy) ,
            ( λ x →
              right-unit ∙ inv (ap-inv h (coherence-square-cocone-span-diagram s c x)))))
      ( up Y)

  is-pushout-transposition-cocone-span-diagram-is-pushout :
    is-pushout s c → is-pushout (transposition-span-diagram s) (transposition-cocone-span-diagram s c)
  is-pushout-transposition-cocone-span-diagram-is-pushout H =
    is-pushout-universal-property-pushout (transposition-span-diagram s)
      ( transposition-cocone-span-diagram s c)
      ( universal-property-pushout-transposition-cocone-span-diagram-universal-property-pushout
        ( universal-property-pushout-is-pushout s c H))
```
