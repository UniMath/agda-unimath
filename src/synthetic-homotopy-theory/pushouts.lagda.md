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
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.functoriality-dependent-pair-types

open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
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
    (f : S → A) (g : S → B) → ((inl-pushout f g) ∘ f) ~ ((inr-pushout f g) ∘ g)

cocone-pushout :
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → cocone f g (pushout f g)
pr1 (cocone-pushout f g) = inl-pushout f g
pr1 (pr2 (cocone-pushout f g)) = inr-pushout f g
pr2 (pr2 (cocone-pushout f g)) = glue-pushout f g

postulate
  up-pushout :
    {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) →
    universal-property-pushout l4 f g (cocone-pushout f g)

equiv-up-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4) → (pushout f g → X) ≃ (cocone f g X)
pr1 (equiv-up-pushout f g X) = cocone-map f g (cocone-pushout f g)
pr2 (equiv-up-pushout f g X) = up-pushout f g X
```

## Definitions

### The cogap map

```agda
cogap :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  { X : UU l4} → cocone f g X → pushout f g → X
cogap f g {X} = map-inv-equiv (equiv-up-pushout f g X)
```

### The predicate of being a pushout cocone

```agda
is-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-pushout f g c = is-equiv (cogap f g c)
```

## Properties

### The pushout of a span has the dependent universal property

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  where

  dependent-up-pushout :
    (f : S → A) (g : S → B) →
    dependent-universal-property-pushout l4 f g (cocone-pushout f g)
  dependent-up-pushout f g =
    dependent-universal-property-universal-property-pushout
    ( f)
    ( g)
    ( cocone-pushout f g)
    ( λ l → up-pushout f g)
    ( l4)
```

### Computation with the cogap map

```agda
module _
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B)
  { X : UU l4} (c : cocone f g X)
  where

  compute-inl-cogap :
    ( a : A) → cogap f g c (inl-pushout f g a) ＝ horizontal-map-cocone f g c a
  compute-inl-cogap =
    horizontal-htpy-cocone-map-universal-property-pushout
      ( f)
      ( g)
      ( cocone-pushout f g)
      ( up-pushout f g)
      ( c)

  compute-inr-cogap :
    ( b : B) → cogap f g c (inr-pushout f g b) ＝ vertical-map-cocone f g c b
  compute-inr-cogap =
    vertical-htpy-cocone-map-universal-property-pushout
      ( f)
      ( g)
      ( cocone-pushout f g)
      ( up-pushout f g)
      ( c)

  compute-glue-cogap :
    statement-coherence-htpy-cocone f g
      ( cocone-map f g (cocone-pushout f g) (cogap f g c))
      ( c)
      ( compute-inl-cogap)
      ( compute-inr-cogap)
  compute-glue-cogap =
    coherence-htpy-cocone-map-universal-property-pushout
      ( f)
      ( g)
      ( cocone-pushout f g)
      ( up-pushout f g)
      ( c)
```

### Fibers of the cogap map

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

  vertical-map-span-cogap-fiber :
    fiber (horizontal-map-cocone f g c ∘ f) x →
    fiber (vertical-map-cocone f g c) x
  vertical-map-span-cogap-fiber =
    -- Choosen to make a coherence square commute almost trivially
    ( map-inv-equiv equiv-fiber-vertical-map-cocone-cogap-inr) ∘
    ( horizontal-map-span-flattening-pushout
      ( λ y → (cogap f g c y) ＝ x) f g (cocone-pushout f g)) ∘
    ( map-equiv equiv-fiber-horizontal-map-cocone-cogap-inl-horizontal-span)

{-
  statement-span-cocone-cogap-fiber : {!!}
  statement-span-cocone-cogap-fiber =
    ( Σ
      ( fiber (horizontal-map-cocone f g c ∘ f) x →
        fiber (horizontal-map-cocone f g c) x)
      ( λ f' →
        ( Σ
          ( fiber (horizontal-map-cocone f g c ∘ f) x →
            fiber (vertical-map-cocone f g c) x)
          ( λ g' → cocone f' g' (fiber (cogap f g c) x)))))
-}

  statement-universal-property-pushout-cogap-fiber : UUω
  statement-universal-property-pushout-cogap-fiber =
    { l : Level} →
    ( Σ
      ( cocone
        ( horizontal-map-span-cogap-fiber)
        ( vertical-map-span-cogap-fiber)
        ( fiber (cogap f g c) x))
      ( λ c →
        universal-property-pushout l
        ( horizontal-map-span-cogap-fiber)
        ( vertical-map-span-cogap-fiber)
        ( c)))

  universal-property-pushout-cogap-fiber :
    statement-universal-property-pushout-cogap-fiber
  pr1 universal-property-pushout-cogap-fiber = _
  pr2 universal-property-pushout-cogap-fiber =
    universal-property-pushout-extended-by-equivalences
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
        ( dependent-up-pushout f g))
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

{-
  S' : UU (l1 ⊔ l4)
  S' = fiber (cogap f g c ∘ inl-pushout f g ∘ f) x

  A' : UU (l2 ⊔ l4)
  A' = fiber (cogap f g c ∘ inl-pushout f g) x

  B' : UU (l3 ⊔ l4)
  B' = fiber (cogap f g c ∘ inr-pushout f g) x

  f' : S' → A'
  f' = map-Σ-map-base f (λ a → (cogap f g c ∘ inl-pushout f g) a ＝ x)

  g' : S' → B'
  g' =
    map-Σ
      ( λ b → (cogap f g c ∘ inr-pushout f g) b ＝ x)
      ( g)
      ( λ s → concat (ap (cogap f g c) (inv (glue-pushout f g s))) x)
-}

  private
    P : pushout f g → UU l4
    P y = cogap f g c y ＝ x

  T : UU (l1 ⊔ l4)
  T = fiber (horizontal-map-cocone f g c ∘ f) x

  F : UU (l2 ⊔ l4)
  F = fiber (horizontal-map-cocone f g c) x

  G : UU (l3 ⊔ l4)
  G = fiber (vertical-map-cocone f g c) x

  f' : T → F
  f' = map-Σ-map-base f (λ a → horizontal-map-cocone f g c a ＝ x)

{-
  g' : T → G
  g' =
    map-Σ
      ( λ b → vertical-map-cocone f g c b ＝ x)
      ( g)
      ( λ s → concat (inv (coherence-square-cocone f g c s)) x)
-}

  k-equiv : T ≃ fiber (cogap f g c ∘ inl-pushout f g ∘ f) x
  k-equiv = equiv-tot (λ s → equiv-concat (compute-inl-cogap f g c (f s)) x)

  i-equiv : F ≃ fiber (cogap f g c ∘ inl-pushout f g) x
  i-equiv = equiv-tot (λ a → equiv-concat (compute-inl-cogap f g c a) x)

  j-equiv : G ≃ fiber (cogap f g c ∘ inr-pushout f g) x
  j-equiv = equiv-tot (λ b → equiv-concat (compute-inr-cogap f g c b) x)

  g' : T → G
  g' =
    map-inv-equiv j-equiv ∘
    horizontal-map-span-flattening-pushout P f g (cocone-pushout f g) ∘
    map-equiv k-equiv

  coh-l :
    coherence-square-maps
      ( map-equiv k-equiv)
      ( f')
      ( vertical-map-span-flattening-pushout P f g (cocone-pushout f g))
      ( map-equiv i-equiv)
  coh-l _ = refl

  coh-r :
    coherence-square-maps
      ( g')
      ( map-equiv k-equiv)
      ( map-equiv j-equiv)
      ( horizontal-map-span-flattening-pushout P f g (cocone-pushout f g))
  coh-r _ = inv (is-section-map-inv-equiv j-equiv _)

  test :
    {l : Level} →
    universal-property-pushout l f' g'
    (comp-cocone-hom-span
      ( vertical-map-span-flattening-pushout P f g (cocone-pushout f g))
      ( horizontal-map-span-flattening-pushout P f g (cocone-pushout f g))
      ( f')
      ( g')
      ( map-equiv i-equiv)
      ( map-equiv j-equiv)
      ( map-equiv k-equiv)
      ( cocone-flattening-pushout P f g (cocone-pushout f g)) coh-l coh-r)
  test =
    universal-property-pushout-extended-by-equivalences
      ( vertical-map-span-flattening-pushout P f g (cocone-pushout f g))
      ( horizontal-map-span-flattening-pushout P f g (cocone-pushout f g))
      ( f')
      ( g')
      ( map-equiv i-equiv) -- TO DO: Fold up lemmas as ≃
      ( map-equiv j-equiv)
      ( map-equiv k-equiv)
      ( cocone-flattening-pushout P f g (cocone-pushout f g))
      ( flattening-lemma-pushout P f g
        ( cocone-pushout f g)
        ( dependent-up-pushout f g))
      ( coh-l)
      ( coh-r)
      ( is-equiv-map-equiv i-equiv)
      ( is-equiv-map-equiv j-equiv)
      ( is-equiv-map-equiv k-equiv)

{-
  universal-property-pushout-cogap-map-fibers : {l : Level} → {!universal-property-pushout!}
  universal-property-pushout-cogap-map-fibers =
    flattening-lemma-pushout P f g
      ( cocone-pushout f g)
      ( dependent-up-pushout f g)
      ( X)
-}
```
