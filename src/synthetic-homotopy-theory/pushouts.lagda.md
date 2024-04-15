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
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import reflection.erasing-equality

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.induction-principle-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Consider a span `𝒮` of types

```text
      f     g
  A <--- S ---> B.
```

A **pushout** of `𝒮` is an initial type `X` equipped with a
[cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) of `𝒮` in
`X`. In other words, a pushout `X` of `𝒮` comes equipped with a cocone structure
`(i , j , H)` where

```text
        g
    S -----> B
    |        |
  f |   H    | j
    V        V
    A -----> X,
        i
```

such that for any type `Y`, the following evaluation map is an equivalence

```text
  (X → Y) → cocone 𝒮 Y.
```

This condition is the
[universal property of the pushout](synthetic-homotopy-theory.universal-property-pushouts.md)
of `𝒮`.

The idea is that the pushout of `𝒮` is the universal type that contains the
elements of the types `A` and `B` via the 'inclusions' `i : A → X` and
`j : B → X`, and furthermore an identification `i a ＝ j b` for every `s : S`
such that `f s ＝ a` and `g s ＝ b`.

Examples of pushouts include
[suspensions](synthetic-homotopy-theory.suspensions-of-types.md),
[spheres](synthetic-homotopy-theory.spheres.md),
[joins](synthetic-homotopy-theory.joins-of-types.md), and the
[smash product](synthetic-homotopy-theory.smash-products-of-pointed-types.md).

## Postulates

### The standard pushout type

We will assume that for any span

```text
      f     g
  A <--- S ---> B,
```

where `S : UU l1`, `A : UU l2`, and `B : UU l3` there is a pushout in
`UU (l1 ⊔ l2 ⊔ l3)`.

```agda
postulate
  pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → UU (l1 ⊔ l2 ⊔ l3)

postulate
  inl-pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → A → pushout f g

postulate
  inr-pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → B → pushout f g

postulate
  glue-pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → inl-pushout f g ∘ f ~ inr-pushout f g ∘ g

cocone-pushout :
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → cocone f g (pushout f g)
pr1 (cocone-pushout f g) = inl-pushout f g
pr1 (pr2 (cocone-pushout f g)) = inr-pushout f g
pr2 (pr2 (cocone-pushout f g)) = glue-pushout f g
```

### The dependent cogap map

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {P : pushout f g → UU l4}
  (c : dependent-cocone f g (cocone-pushout f g) P)
  where

  postulate
    dependent-cogap : (x : pushout f g) → P x

  compute-inl-dependent-cogap :
    (a : A) →
    dependent-cogap (inl-pushout f g a) ＝
    horizontal-map-dependent-cocone f g (cocone-pushout f g) P c a
  compute-inl-dependent-cogap a = primEraseEquality compute-inl-dependent-cogap'
    where postulate
      compute-inl-dependent-cogap' :
        dependent-cogap (inl-pushout f g a) ＝
        horizontal-map-dependent-cocone f g (cocone-pushout f g) P c a

  compute-inr-dependent-cogap :
    (b : B) →
    dependent-cogap (inr-pushout f g b) ＝
    vertical-map-dependent-cocone f g (cocone-pushout f g) P c b
  compute-inr-dependent-cogap b = primEraseEquality compute-inr-dependent-cogap'
    where postulate
      compute-inr-dependent-cogap' :
        dependent-cogap (inr-pushout f g b) ＝
        vertical-map-dependent-cocone f g (cocone-pushout f g) P c b

  postulate
    compute-glue-dependent-cogap :
      coherence-htpy-dependent-cocone f g
        (cocone-pushout f g)
        ( P)
        ( dependent-cocone-map f g (cocone-pushout f g) P dependent-cogap)
        ( c)
        ( compute-inl-dependent-cogap)
        ( compute-inr-dependent-cogap)
```

## Definitions

### The induction principle of standard pushouts

```agda
module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B)
  where

  is-section-dependent-cogap :
    {l : Level} {P : pushout f g → UU l} →
    is-section
      ( dependent-cocone-map f g (cocone-pushout f g) P)
      ( dependent-cogap f g)
  is-section-dependent-cogap {P = P} c =
    eq-htpy-dependent-cocone f g
      ( cocone-pushout f g)
      ( P)
      ( dependent-cocone-map f g (cocone-pushout f g) P (dependent-cogap f g c))
      ( c)
      ( compute-inl-dependent-cogap f g c ,
        compute-inr-dependent-cogap f g c ,
        compute-glue-dependent-cogap f g c)

  induction-principle-pushout' :
    {l : Level} → induction-principle-pushout l f g (cocone-pushout f g)
  induction-principle-pushout' P =
    ( dependent-cogap f g , is-section-dependent-cogap)
```

### The dependent universal property of standard pushouts

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B)
  where

  dup-pushout :
    dependent-universal-property-pushout l4 f g (cocone-pushout f g)
  dup-pushout =
    dependent-universal-property-pushout-induction-principle-pushout f g
      ( cocone-pushout f g)
      ( induction-principle-pushout' f g)

  equiv-dup-pushout :
    (P : pushout f g → UU l4) →
    ((x : pushout f g) → P x) ≃ dependent-cocone f g (cocone-pushout f g) P
  pr1 (equiv-dup-pushout P) =
    dependent-cocone-map f g (cocone-pushout f g) P
  pr2 (equiv-dup-pushout P) =
    dup-pushout P

  is-retraction-dependent-cogap :
    {P : pushout f g → UU l4} →
    is-retraction
      ( dependent-cocone-map f g (cocone-pushout f g) P)
      ( dependent-cogap f g)
  is-retraction-dependent-cogap {P = P} =
    is-retraction-map-inv-is-equiv (dup-pushout P)
```

### The cogap map

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4}
  where

  cogap : cocone f g X → pushout f g → X
  cogap = dependent-cogap f g ∘ dependent-cocone-cocone f g (cocone-pushout f g)
```

We write out the section and retraction homotopy in full detail to ensure that
the inverse of `cocone-map` computes to `cogap` judgmentally.

```agda
  is-section-cogap : is-section (cocone-map f g (cocone-pushout f g)) cogap
  is-section-cogap =
    ( ( triangle-dependent-cocone-map-constant-type-family' f g
        ( cocone-pushout f g)) ·r
      ( cogap)) ∙h
    ( ( map-inv-dependent-cocone-cocone f g (cocone-pushout f g)) ·l
      ( is-section-dependent-cogap f g) ·r
      ( dependent-cocone-cocone f g (cocone-pushout f g))) ∙h
    ( is-retraction-map-inv-dependent-cocone-cocone f g (cocone-pushout f g))

  is-retraction-cogap :
    is-retraction (cocone-map f g (cocone-pushout f g)) cogap
  is-retraction-cogap =
    ( ( cogap) ·l
      ( triangle-dependent-cocone-map-constant-type-family' f g
        ( cocone-pushout f g))) ∙h
    ( ( dependent-cogap f g) ·l
      ( is-section-map-inv-dependent-cocone-cocone f g (cocone-pushout f g)) ·r
      ( dependent-cocone-map f g (cocone-pushout f g) (λ _ → X))) ∙h
    ( is-retraction-dependent-cogap f g)
```

### The universal property of standard pushouts

```agda
up-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) →
  universal-property-pushout l4 f g (cocone-pushout f g)
up-pushout f g P =
  is-equiv-is-invertible
    ( cogap f g)
    ( is-section-cogap f g)
    ( is-retraction-cogap f g)

equiv-up-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4) → (pushout f g → X) ≃ (cocone f g X)
pr1 (equiv-up-pushout f g X) = cocone-map f g (cocone-pushout f g)
pr2 (equiv-up-pushout f g X) = up-pushout f g X
```

### Computation with the cogap map

```agda
module _
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B)
  { X : UU l4} (c : cocone f g X)
  where

  compute-inl-cogap :
    cogap f g c ∘ inl-pushout f g ~ horizontal-map-cocone f g c
  compute-inl-cogap =
    compute-inl-dependent-cogap f g
      ( dependent-cocone-cocone f g (cocone-pushout f g) c)

  compute-inr-cogap :
    cogap f g c ∘ inr-pushout f g ~ vertical-map-cocone f g c
  compute-inr-cogap =
    compute-inr-dependent-cogap f g
      ( dependent-cocone-cocone f g (cocone-pushout f g) c)

  -- compute-glue-cogap :
  --   statement-coherence-htpy-cocone f g
  --     ( cocone-map f g (cocone-pushout f g) (cogap f g c))
  --     ( c)
  --     ( compute-inl-cogap)
  --     ( compute-inr-cogap)
  -- compute-glue-cogap =
  --   coherence-htpy-cocone-map-universal-property-pushout
  --     ( f)
  --     ( g)
  --     ( cocone-pushout f g)
  --     ( up-pushout f g)
  --     ( c)
```

### The small predicate of being a pushout cocone

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  is-pushout : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pushout = is-equiv (cogap f g c)

  is-prop-is-pushout : is-prop is-pushout
  is-prop-is-pushout = is-property-is-equiv (cogap f g c)

  is-pushout-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-pushout-Prop = is-pushout
  pr2 is-pushout-Prop = is-prop-is-pushout
```

## Properties

### Pushout cocones satisfy the universal property of the pushout

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  universal-property-pushout-is-pushout :
    is-pushout f g c → {l : Level} → universal-property-pushout l f g c
  universal-property-pushout-is-pushout po =
    up-pushout-up-pushout-is-equiv f g
      ( cocone-pushout f g)
      ( c)
      ( cogap f g c)
      ( htpy-cocone-map-universal-property-pushout f g
        ( cocone-pushout f g)
        ( up-pushout f g)
        ( c))
      ( po)
      ( up-pushout f g)

  is-pushout-universal-property-pushout :
    ({l : Level} → universal-property-pushout l f g c) → is-pushout f g c
  is-pushout-universal-property-pushout =
    is-equiv-up-pushout-up-pushout f g
      ( cocone-pushout f g)
      ( c)
      ( cogap f g c)
      ( htpy-cocone-map-universal-property-pushout f g
        ( cocone-pushout f g)
        ( up-pushout f g)
        ( c))
      ( up-pushout f g)
```

### Fibers of the cogap map

We characterize the [fibers](foundation-core.fibers-of-maps.md) of the cogap map
as a pushout of fibers. This is an application of the
[flattening lemma for pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md).

Given a pushout square with a
[cocone](synthetic-homotopy-theory.cocones-under-spans.md)

```text
       g
   S ----> B
   |       | \
 f |    inr|  \  n
   v    ⌜  v   \
   A ----> ∙    \
    \ inl   \   |
  m  \  cogap\  |
      \       ∨ v
       \-----> X
```

we have, for every `x : X`, a pushout square of fibers:

```text
    fiber (m ∘ f) x ---> fiber (cogap ∘ inr) x
           |                       |
           |                       |
           v                    ⌜  v
 fiber (cogap ∘ inl) x ----> fiber cogap x
```

```agda
module _
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B)
  { X : UU l4} (c : cocone f g X) (x : X)
  where

  equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-span :
    fiber (horizontal-map-cocone f g c ∘ f) x ≃
    fiber (cogap f g c ∘ inl-pushout f g ∘ f) x
  equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-span =
    equiv-tot (λ s → equiv-concat (compute-inl-cogap f g c (f s)) x)

  equiv-fiber-horizontal-map-cocone-cogap-inl :
    fiber (horizontal-map-cocone f g c) x ≃
    fiber (cogap f g c ∘ inl-pushout f g) x
  equiv-fiber-horizontal-map-cocone-cogap-inl =
    equiv-tot (λ a → equiv-concat (compute-inl-cogap f g c a) x)

  equiv-fiber-vertical-map-cocone-cogap-inr :
    fiber (vertical-map-cocone f g c) x ≃
    fiber (cogap f g c ∘ inr-pushout f g) x
  equiv-fiber-vertical-map-cocone-cogap-inr =
    equiv-tot (λ b → equiv-concat (compute-inr-cogap f g c b) x)

  horizontal-map-span-cogap-fiber :
    fiber (horizontal-map-cocone f g c ∘ f) x →
    fiber (horizontal-map-cocone f g c) x
  horizontal-map-span-cogap-fiber =
    map-Σ-map-base f (λ a → horizontal-map-cocone f g c a ＝ x)
```

Since our pushout square of fibers has `fiber (m ∘ f) x` as its top-left corner
and not `fiber (n ∘ g) x`, things are "left-biased". For this reason, the
following map is constructed as a composition which makes a later coherence
square commute (almost) trivially.

```agda
  vertical-map-span-cogap-fiber :
    fiber (horizontal-map-cocone f g c ∘ f) x →
    fiber (vertical-map-cocone f g c) x
  vertical-map-span-cogap-fiber =
    ( map-inv-equiv equiv-fiber-vertical-map-cocone-cogap-inr) ∘
    ( horizontal-map-span-flattening-pushout
      ( λ y → (cogap f g c y) ＝ x) f g (cocone-pushout f g)) ∘
    ( map-equiv equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-span)

  statement-universal-property-pushout-cogap-fiber : UUω
  statement-universal-property-pushout-cogap-fiber =
    { l : Level} →
    Σ ( cocone
        ( horizontal-map-span-cogap-fiber)
        ( vertical-map-span-cogap-fiber)
        ( fiber (cogap f g c) x))
      ( universal-property-pushout l
        ( horizontal-map-span-cogap-fiber)
        ( vertical-map-span-cogap-fiber))

  universal-property-pushout-cogap-fiber :
    statement-universal-property-pushout-cogap-fiber
  universal-property-pushout-cogap-fiber =
    universal-property-pushout-extension-by-equivalences
      ( vertical-map-span-flattening-pushout
        ( λ y → cogap f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-pushout f g))
      ( horizontal-map-span-flattening-pushout
        ( λ y → cogap f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-pushout f g))
      ( horizontal-map-span-cogap-fiber)
      ( vertical-map-span-cogap-fiber)
      ( map-equiv equiv-fiber-horizontal-map-cocone-cogap-inl)
      ( map-equiv equiv-fiber-vertical-map-cocone-cogap-inr)
      ( map-equiv equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-span)
      ( cocone-flattening-pushout
        ( λ y → cogap f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-pushout f g))
      ( flattening-lemma-pushout
        ( λ y → cogap f g c y ＝ x)
        ( f)
        ( g)
        ( cocone-pushout f g)
        ( dup-pushout f g))
      ( refl-htpy)
      ( λ _ →
        inv
          ( is-section-map-inv-equiv
            ( equiv-fiber-vertical-map-cocone-cogap-inr)
            ( _)))
      ( is-equiv-map-equiv equiv-fiber-horizontal-map-cocone-cogap-inl)
      ( is-equiv-map-equiv equiv-fiber-vertical-map-cocone-cogap-inr)
      ( is-equiv-map-equiv
        ( equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-span))
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

```agda
  module _
    { l5 l6 l7 : Level} (T : UU l5) (F : UU l6) (G : UU l7)
    ( i : F ≃ fiber (horizontal-map-cocone f g c) x)
    ( j : G ≃ fiber (vertical-map-cocone f g c) x)
    ( k : T ≃ fiber (horizontal-map-cocone f g c ∘ f) x)
    ( u : T → F)
    ( v : T → G)
    ( coh-l :
      coherence-square-maps
        ( map-equiv k)
        ( u)
        ( horizontal-map-span-cogap-fiber)
        ( map-equiv i))
    ( coh-r :
      coherence-square-maps
        ( v)
        ( map-equiv k)
        ( map-equiv j)
        ( vertical-map-span-cogap-fiber))
    where

    universal-property-pushout-cogap-fiber-up-to-equiv :
      { l : Level} →
      ( Σ ( cocone u v (fiber (cogap f g c) x))
          ( λ c → universal-property-pushout l u v c))
    universal-property-pushout-cogap-fiber-up-to-equiv {l} =
      universal-property-pushout-extension-by-equivalences
        ( horizontal-map-span-cogap-fiber)
        ( vertical-map-span-cogap-fiber)
        ( u)
        ( v)
        ( map-equiv i)
        ( map-equiv j)
        ( map-equiv k)
        ( pr1 ( universal-property-pushout-cogap-fiber {l}))
        ( pr2 universal-property-pushout-cogap-fiber)
        ( coh-l)
        ( coh-r)
        ( is-equiv-map-equiv i)
        ( is-equiv-map-equiv j)
        ( is-equiv-map-equiv k)
```

### Swapping a pushout cocone yields another pushout cocone

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4) (c : cocone f g X)
  where

  universal-property-pushout-swap-cocone-universal-property-pushout :
    {l : Level} → universal-property-pushout l f g c →
    universal-property-pushout l g f (swap-cocone f g X c)
  universal-property-pushout-swap-cocone-universal-property-pushout up Y =
    is-equiv-equiv'
      ( id-equiv)
      ( equiv-swap-cocone f g Y)
      ( λ h →
        eq-htpy-cocone g f
          ( swap-cocone f g Y (cocone-map f g c h))
          ( cocone-map g f (swap-cocone f g X c) h)
          ( ( refl-htpy) ,
            ( refl-htpy) ,
            ( λ s →
              right-unit ∙ inv (ap-inv h (coherence-square-cocone f g c s)))))
      ( up Y)

  is-pushout-swap-cocone-is-pushout :
    is-pushout f g c → is-pushout g f (swap-cocone f g X c)
  is-pushout-swap-cocone-is-pushout po =
    is-pushout-universal-property-pushout g f
      ( swap-cocone f g X c)
      ( universal-property-pushout-swap-cocone-universal-property-pushout
        ( universal-property-pushout-is-pushout f g c po))
```
