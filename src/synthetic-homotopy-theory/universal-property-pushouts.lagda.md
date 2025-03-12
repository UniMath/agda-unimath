# The universal property of pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.universal-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.subtype-identity-principle
open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pullback-property-pushouts
```

</details>

## Idea

Consider a span `𝒮` of types

```text
      f     g
  A <--- S ---> B.
```

and a type `X` equipped with a
[cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) of `S` into
`X`. The **universal property of the pushout** of `𝒮` asserts that `X` is the
_initial_ type equipped with such cocone structure. In other words, the
universal property of the pushout of `𝒮` asserts that the following evaluation
map is an equivalence:

```text
  (X → Y) → cocone 𝒮 Y.
```

There are several ways of asserting a condition equivalent to the universal
property of pushouts. The statements and proofs of mutual equivalence may be
found in the following table:

{{#include tables/pushouts.md}}

## Definition

### The universal property of pushouts at a universe level

**Warning.** This definition is here only because of backward compatibility
reasons, and will be removed in the future. Do not use this definition in new
formalizations.

```agda
universal-property-pushout-Level :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
universal-property-pushout-Level l f g c =
  (Y : UU l) → is-equiv (cocone-map f g {Y = Y} c)
```

### The universal property of pushouts

```agda
universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → UUω
universal-property-pushout f g c =
  {l : Level} → universal-property-pushout-Level l f g c

module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  (f : S → A) (g : S → B) (c : cocone f g X)
  (up-c : universal-property-pushout f g c)
  (d : cocone f g Y)
  where

  map-universal-property-pushout : X → Y
  map-universal-property-pushout = map-inv-is-equiv (up-c Y) d

  htpy-cocone-map-universal-property-pushout :
    htpy-cocone f g (cocone-map f g c map-universal-property-pushout) d
  htpy-cocone-map-universal-property-pushout =
    htpy-eq-cocone
      ( f)
      ( g)
      ( cocone-map f g c map-universal-property-pushout)
      ( d)
      ( is-section-map-inv-is-equiv (up-c Y) d)

  horizontal-htpy-cocone-map-universal-property-pushout :
    map-universal-property-pushout ∘ horizontal-map-cocone f g c ~
    horizontal-map-cocone f g d
  horizontal-htpy-cocone-map-universal-property-pushout =
    horizontal-htpy-cocone
      ( f)
      ( g)
      ( cocone-map f g c map-universal-property-pushout)
      ( d)
      ( htpy-cocone-map-universal-property-pushout)

  vertical-htpy-cocone-map-universal-property-pushout :
    map-universal-property-pushout ∘ vertical-map-cocone f g c ~
    vertical-map-cocone f g d
  vertical-htpy-cocone-map-universal-property-pushout =
    vertical-htpy-cocone
      ( f)
      ( g)
      ( cocone-map f g c map-universal-property-pushout)
      ( d)
      ( htpy-cocone-map-universal-property-pushout)

  coherence-htpy-cocone-map-universal-property-pushout :
    statement-coherence-htpy-cocone f g
      ( cocone-map f g c map-universal-property-pushout)
      ( d)
      ( horizontal-htpy-cocone-map-universal-property-pushout)
      ( vertical-htpy-cocone-map-universal-property-pushout)
  coherence-htpy-cocone-map-universal-property-pushout =
    coherence-htpy-cocone
      ( f)
      ( g)
      ( cocone-map f g c map-universal-property-pushout)
      ( d)
      ( htpy-cocone-map-universal-property-pushout)

  uniqueness-map-universal-property-pushout :
    is-contr ( Σ (X → Y) (λ h → htpy-cocone f g (cocone-map f g c h) d))
  uniqueness-map-universal-property-pushout =
    is-contr-is-equiv'
      ( fiber (cocone-map f g c) d)
      ( tot (λ h → htpy-eq-cocone f g (cocone-map f g c h) d))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → is-equiv-htpy-eq-cocone f g (cocone-map f g c h) d))
      ( is-contr-map-is-equiv (up-c Y) d)
```

## Properties

### The 3-for-2 property of pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y)
  ( h : X → Y) (KLM : htpy-cocone f g (cocone-map f g c h) d)
  where

  triangle-map-cocone :
    { l6 : Level} (Z : UU l6) →
    ( cocone-map f g d) ~ (cocone-map f g c ∘ precomp h Z)
  triangle-map-cocone Z k =
    inv
      ( ( cocone-map-comp f g c h k) ∙
        ( ap
          ( λ t → cocone-map f g t k)
          ( eq-htpy-cocone f g (cocone-map f g c h) d KLM)))

  is-equiv-up-pushout-up-pushout :
    universal-property-pushout f g c →
    universal-property-pushout f g d →
    is-equiv h
  is-equiv-up-pushout-up-pushout up-c up-d =
    is-equiv-is-equiv-precomp h
      ( λ Z →
        is-equiv-top-map-triangle
          ( cocone-map f g d)
          ( cocone-map f g c)
          ( precomp h Z)
          ( triangle-map-cocone Z)
          ( up-c Z)
          ( up-d Z))

  up-pushout-up-pushout-is-equiv :
    is-equiv h →
    universal-property-pushout f g c →
    universal-property-pushout f g d
  up-pushout-up-pushout-is-equiv is-equiv-h up-c Z =
    is-equiv-left-map-triangle
      ( cocone-map f g d)
      ( cocone-map f g c)
      ( precomp h Z)
      ( triangle-map-cocone Z)
      ( is-equiv-precomp-is-equiv h is-equiv-h Z)
      ( up-c Z)

  up-pushout-is-equiv-up-pushout :
    universal-property-pushout f g d →
    is-equiv h →
    universal-property-pushout f g c
  up-pushout-is-equiv-up-pushout up-d is-equiv-h Z =
    is-equiv-right-map-triangle
      ( cocone-map f g d)
      ( cocone-map f g c)
      ( precomp h Z)
      ( triangle-map-cocone Z)
      ( up-d Z)
      ( is-equiv-precomp-is-equiv h is-equiv-h Z)
```

### Pushouts are uniquely unique

```agda
uniquely-unique-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y) →
  universal-property-pushout f g c →
  universal-property-pushout f g d →
  is-contr
    ( Σ (X ≃ Y) (λ e → htpy-cocone f g (cocone-map f g c (map-equiv e)) d))
uniquely-unique-pushout f g c d up-c up-d =
  is-torsorial-Eq-subtype
    ( uniqueness-map-universal-property-pushout f g c up-c d)
    ( is-property-is-equiv)
    ( map-universal-property-pushout f g c up-c d)
    ( htpy-cocone-map-universal-property-pushout f g c up-c d)
    ( is-equiv-up-pushout-up-pushout f g c d
      ( map-universal-property-pushout f g c up-c d)
      ( htpy-cocone-map-universal-property-pushout f g c up-c d)
      ( up-c)
      ( up-d))
```

### The universal property of pushouts is equivalent to the pullback property of pushouts

In order to show that the universal property of pushouts is equivalent to the
pullback property, we show that the maps `cocone-map` and the gap map fit in a
commuting triangle, where the third map is an equivalence. The claim then
follows from the 3-for-2 property of equivalences.

```agda
triangle-pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  cocone-map f g c ~
  ( tot (λ i' → tot (λ j' → htpy-eq)) ∘
    gap (_∘ f) (_∘ g) (cone-pullback-property-pushout f g c Y))
triangle-pullback-property-pushout-universal-property-pushout f g c Y h =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( inv (is-section-eq-htpy (h ·l coherence-square-cocone f g c))))

pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  universal-property-pushout f g c → pullback-property-pushout f g c
pullback-property-pushout-universal-property-pushout f g c up-c Y =
  is-equiv-top-map-triangle
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' → htpy-eq)))
    ( gap (_∘ f) (_∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' →
        is-equiv-tot-is-fiberwise-equiv (λ j' → funext (i' ∘ f) (j' ∘ g))))
    ( up-c Y)

universal-property-pushout-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  pullback-property-pushout f g c → universal-property-pushout f g c
universal-property-pushout-pullback-property-pushout f g c pb-c Y =
  is-equiv-left-map-triangle
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' → htpy-eq)))
    ( gap (_∘ f) (_∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( pb-c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' →
        is-equiv-tot-is-fiberwise-equiv (λ j' → funext (i' ∘ f) (j' ∘ g))))
```

### If the vertical map of a span is an equivalence, then the vertical map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f →
  universal-property-pushout f g c →
  is-equiv (vertical-map-cocone f g c)
is-equiv-universal-property-pushout f g (i , j , H) is-equiv-f up-c =
  is-equiv-is-equiv-precomp j
    ( λ T →
      is-equiv-horizontal-map-is-pullback
        ( _∘ f)
        ( _∘ g)
        ( cone-pullback-property-pushout f g (i , j , H) T)
        ( is-equiv-precomp-is-equiv f is-equiv-f T)
        ( pullback-property-pushout-universal-property-pushout f g
          ( i , j , H)
          ( up-c)
          ( T)))

equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (e : S ≃ A) (g : S → B) (c : cocone (map-equiv e) g C) →
  universal-property-pushout (map-equiv e) g c →
  B ≃ C
pr1 (equiv-universal-property-pushout e g c up-c) =
  vertical-map-cocone (map-equiv e) g c
pr2 (equiv-universal-property-pushout e g c up-c) =
  is-equiv-universal-property-pushout
    ( map-equiv e)
    ( g)
    ( c)
    ( is-equiv-map-equiv e)
    ( up-c)

universal-property-pushout-is-equiv :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f → is-equiv (vertical-map-cocone f g c) →
  universal-property-pushout f g c
universal-property-pushout-is-equiv
  f g (i , j , H) is-equiv-f is-equiv-j {l} =
  let c = (i , j , H) in
  universal-property-pushout-pullback-property-pushout f g c
    ( λ T →
      is-pullback-is-equiv-horizontal-maps
        ( _∘ f)
        ( _∘ g)
        ( cone-pullback-property-pushout f g c T)
        ( is-equiv-precomp-is-equiv f is-equiv-f T)
        ( is-equiv-precomp-is-equiv j is-equiv-j T))
```

### If the horizontal map of a span is an equivalence, then the horizontal map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g →
  universal-property-pushout f g c →
  is-equiv (horizontal-map-cocone f g c)
is-equiv-universal-property-pushout' f g c is-equiv-g up-c =
  is-equiv-is-equiv-precomp
    ( horizontal-map-cocone f g c)
    ( λ T →
      is-equiv-vertical-map-is-pullback
        ( precomp f T)
        ( precomp g T)
        ( cone-pullback-property-pushout f g c T)
        ( is-equiv-precomp-is-equiv g is-equiv-g T)
        ( pullback-property-pushout-universal-property-pushout f g c up-c T))

equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (e : S ≃ B) (c : cocone f (map-equiv e) C) →
  universal-property-pushout f (map-equiv e) c →
  A ≃ C
pr1 (equiv-universal-property-pushout' f e c up-c) = pr1 c
pr2 (equiv-universal-property-pushout' f e c up-c) =
  is-equiv-universal-property-pushout'
    ( f)
    ( map-equiv e)
    ( c)
    ( is-equiv-map-equiv e)
    ( up-c)

universal-property-pushout-is-equiv' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g → is-equiv (pr1 c) →
  universal-property-pushout f g c
universal-property-pushout-is-equiv' f g (i , j , H) is-equiv-g is-equiv-i {l} =
  let c = (i , j , H) in
  universal-property-pushout-pullback-property-pushout f g c
    ( λ T →
      is-pullback-is-equiv-vertical-maps
        ( precomp f T)
        ( precomp g T)
        ( cone-pullback-property-pushout f g c T)
        ( is-equiv-precomp-is-equiv g is-equiv-g T)
        ( is-equiv-precomp-is-equiv i is-equiv-i T))
```

### The pushout pasting lemmas

#### The horizontal pushout pasting lemma

If in the following diagram the left square is a pushout, then the outer
rectangle is a pushout if and only if the right square is a pushout.

```text
       g       k
    A ----> B ----> C
    |       |       |
  f |       |       |
    ∨       ∨       ∨
    X ----> Y ----> Z
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → X) (g : A → B) (k : B → C)
  ( c : cocone f g Y) (d : cocone (vertical-map-cocone f g c) k Z)
  ( up-c : universal-property-pushout f g c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-right :
    universal-property-pushout (vertical-map-cocone f g c) k d →
    universal-property-pushout f (k ∘ g) (cocone-comp-horizontal f g k c d)
  universal-property-pushout-rectangle-universal-property-pushout-right
    ( up-d)
    { l} =
    universal-property-pushout-pullback-property-pushout f
      ( k ∘ g)
      ( cocone-comp-horizontal f g k c d)
      ( λ W →
        tr
          ( is-pullback (precomp f W) (precomp (k ∘ g) W))
          ( inv
            ( eq-htpy-cone
              ( precomp f W)
              ( precomp (k ∘ g) W)
              ( cone-pullback-property-pushout
                ( f)
                ( k ∘ g)
                ( cocone-comp-horizontal f g k c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp f W)
                ( precomp g W)
                ( precomp k W)
                ( cone-pullback-property-pushout f g c W)
                ( cone-pullback-property-pushout
                  ( vertical-map-cocone f g c)
                  ( k)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( g)
                  ( k)
                  ( f)
                  ( vertical-map-cocone f g c)
                  ( vertical-map-cocone (vertical-map-cocone f g c) k d)
                  ( horizontal-map-cocone f g c)
                  ( horizontal-map-cocone (vertical-map-cocone f g c) k d)
                  ( coherence-square-cocone f g c)
                  ( coherence-square-cocone (vertical-map-cocone f g c) k d)))))
          ( is-pullback-rectangle-is-pullback-top-square
            ( precomp f W)
            ( precomp g W)
            ( precomp k W)
            ( cone-pullback-property-pushout f g c W)
            ( cone-pullback-property-pushout (vertical-map-cocone f g c) k d W)
            ( pullback-property-pushout-universal-property-pushout f g c
              ( up-c)
              ( W))
            ( pullback-property-pushout-universal-property-pushout
              ( vertical-map-cocone f g c)
              ( k)
              ( d)
              ( up-d)
              ( W))))

  universal-property-pushout-right-universal-property-pushout-rectangle :
    universal-property-pushout f (k ∘ g) (cocone-comp-horizontal f g k c d) →
    universal-property-pushout (vertical-map-cocone f g c) k d
  universal-property-pushout-right-universal-property-pushout-rectangle
    ( up-r)
    { l} =
    universal-property-pushout-pullback-property-pushout
      ( vertical-map-cocone f g c)
      ( k)
      ( d)
      ( λ W →
        is-pullback-top-square-is-pullback-rectangle
          ( precomp f W)
          ( precomp g W)
          ( precomp k W)
          ( cone-pullback-property-pushout f g c W)
          ( cone-pullback-property-pushout (vertical-map-cocone f g c) k d W)
          ( pullback-property-pushout-universal-property-pushout f g c
            ( up-c)
            ( W))
          ( tr
            ( is-pullback (precomp f W) (precomp (k ∘ g) W))
            ( eq-htpy-cone
              ( precomp f W)
              ( precomp (k ∘ g) W)
              ( cone-pullback-property-pushout f
                ( k ∘ g)
                ( cocone-comp-horizontal f g k c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp f W)
                ( precomp g W)
                ( precomp k W)
                ( cone-pullback-property-pushout f g c W)
                ( cone-pullback-property-pushout
                  ( vertical-map-cocone f g c)
                  ( k)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( g)
                  ( k)
                  ( f)
                  ( vertical-map-cocone f g c)
                  ( vertical-map-cocone (vertical-map-cocone f g c) k d)
                  ( horizontal-map-cocone f g c)
                  ( horizontal-map-cocone (vertical-map-cocone f g c) k d)
                  ( coherence-square-cocone f g c)
                  ( coherence-square-cocone (vertical-map-cocone f g c) k d))))
            ( pullback-property-pushout-universal-property-pushout f
              ( k ∘ g)
              ( cocone-comp-horizontal f g k c d)
              ( up-r)
              ( W))))
```

#### Extending pushouts by equivalences on the left

As a special case of the horizontal pushout pasting lemma we can extend a
pushout square by equivalences on the left.

If we have a pushout square on the right, equivalences S' ≃ S and A' ≃ A, and a
map f' : S' → A' making the left square commute, then the outer rectangle is
again a pushout.

```text
         i       g
     S' ---> S ----> B
     |   ≃   |       |
  f' |       | f     |
     ∨   ≃   ∨     ⌜ ∨
     A' ---> A ----> X
         j
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {S' : UU l5} {A' : UU l6}
  ( f : S → A) (g : S → B) (i : S' → S) (j : A' → A) (f' : S' → A')
  ( c : cocone f g X)
  ( up-c : universal-property-pushout f g c)
  ( coh : coherence-square-maps i f' f j)
  where

  universal-property-pushout-left-extended-by-equivalences :
    is-equiv i → is-equiv j →
    universal-property-pushout
      ( f')
      ( g ∘ i)
      ( cocone-comp-horizontal' f' i g f j c coh)
  universal-property-pushout-left-extended-by-equivalences ie je =
    universal-property-pushout-rectangle-universal-property-pushout-right f' i g
      ( j , f , coh)
      ( c)
      ( universal-property-pushout-is-equiv' f' i (j , f , coh) ie je)
      ( up-c)

  universal-property-pushout-left-extension-by-equivalences :
    {l : Level} → is-equiv i → is-equiv j →
    Σ (cocone f' (g ∘ i) X) (universal-property-pushout-Level l f' (g ∘ i))
  pr1 (universal-property-pushout-left-extension-by-equivalences ie je) =
    cocone-comp-horizontal' f' i g f j c coh
  pr2 (universal-property-pushout-left-extension-by-equivalences ie je) =
    universal-property-pushout-left-extended-by-equivalences ie je
```

#### The vertical pushout pasting lemma

If in the following diagram the top square is a pushout, then the outer
rectangle is a pushout if and only if the bottom square is a pushout.

```text
        g
    A -----> X
    |        |
  f |        |
    ∨      ⌜ ∨
    B -----> Y
    |        |
  k |        |
    ∨        ∨
    C -----> Z
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → B) (g : A → X) (k : B → C)
  ( c : cocone f g Y) (d : cocone k (horizontal-map-cocone f g c) Z)
  ( up-c : universal-property-pushout f g c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-top :
    universal-property-pushout k (horizontal-map-cocone f g c) d →
    universal-property-pushout (k ∘ f) g (cocone-comp-vertical f g k c d)
  universal-property-pushout-rectangle-universal-property-pushout-top up-d =
    universal-property-pushout-pullback-property-pushout
      ( k ∘ f)
      ( g)
      ( cocone-comp-vertical f g k c d)
      ( λ W →
        tr
          ( is-pullback (precomp (k ∘ f) W) (precomp g W))
          ( inv
            ( eq-htpy-cone
              ( precomp (k ∘ f) W)
              ( precomp g W)
              ( cone-pullback-property-pushout
                ( k ∘ f)
                ( g)
                ( cocone-comp-vertical f g k c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp k W)
                ( precomp f W)
                ( precomp g W)
                ( cone-pullback-property-pushout f g c W)
                ( cone-pullback-property-pushout k
                  ( horizontal-map-cocone f g c)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( g)
                  ( f)
                  ( vertical-map-cocone f g c)
                  ( horizontal-map-cocone f g c)
                  ( k)
                  ( vertical-map-cocone k (horizontal-map-cocone f g c) d)
                  ( horizontal-map-cocone k (horizontal-map-cocone f g c) d)
                  ( coherence-square-cocone f g c)
                  ( coherence-square-cocone k
                    ( horizontal-map-cocone f g c)
                    ( d))))))
          ( is-pullback-rectangle-is-pullback-left-square
            ( precomp k W)
            ( precomp f W)
            ( precomp g W)
            ( cone-pullback-property-pushout f g c W)
            ( cone-pullback-property-pushout k
              ( horizontal-map-cocone f g c)
              ( d)
              ( W))
            ( pullback-property-pushout-universal-property-pushout f g c
              ( up-c)
              ( W))
            ( pullback-property-pushout-universal-property-pushout k
              ( horizontal-map-cocone f g c)
              ( d)
              ( up-d)
              ( W))))

  universal-property-pushout-top-universal-property-pushout-rectangle :
    universal-property-pushout (k ∘ f) g (cocone-comp-vertical f g k c d) →
    universal-property-pushout k (horizontal-map-cocone f g c) d
  universal-property-pushout-top-universal-property-pushout-rectangle up-r =
    universal-property-pushout-pullback-property-pushout k
      ( horizontal-map-cocone f g c)
      ( d)
      ( λ W →
        is-pullback-left-square-is-pullback-rectangle
          ( precomp k W)
          ( precomp f W)
          ( precomp g W)
          ( cone-pullback-property-pushout f g c W)
          ( cone-pullback-property-pushout k (horizontal-map-cocone f g c) d W)
          ( pullback-property-pushout-universal-property-pushout f g c up-c W)
          ( tr
            ( is-pullback (precomp (k ∘ f) W) (precomp g W))
            ( eq-htpy-cone
              ( precomp (k ∘ f) W)
              ( precomp g W)
              ( cone-pullback-property-pushout
                ( k ∘ f)
                ( g)
                ( cocone-comp-vertical f g k c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp k W)
                ( precomp f W)
                ( precomp g W)
                ( cone-pullback-property-pushout f g c W)
                ( cone-pullback-property-pushout k
                  ( horizontal-map-cocone f g c)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( g)
                  ( f)
                  ( vertical-map-cocone f g c)
                  ( horizontal-map-cocone f g c)
                  ( k)
                  ( vertical-map-cocone k
                    ( horizontal-map-cocone f g c)
                    ( d))
                  ( horizontal-map-cocone k
                    ( horizontal-map-cocone f g c)
                    ( d))
                  ( coherence-square-cocone f g c)
                  ( coherence-square-cocone k
                    ( horizontal-map-cocone f g c)
                    ( d)))))
            ( pullback-property-pushout-universal-property-pushout (k ∘ f) g
              ( cocone-comp-vertical f g k c d)
              ( up-r)
              ( W))))
```

#### Extending pushouts by equivalences at the top

If we have a pushout square on the right, equivalences `S' ≃ S` and `B' ≃ B`,
and a map `g' : S' → B'` making the top square commute, then the vertical
rectangle is again a pushout. This is a special case of the vertical pushout
pasting lemma.

```text
          g'
      S' ---> B'
      |       |
    i | ≃   ≃ | j
      ∨   g   ∨
      S ----> B
      |       |
    f |       |
      ∨     ⌜ ∨
      A ----> X
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {S' : UU l5} {B' : UU l6}
  ( f : S → A) (g : S → B) (i : S' → S) (j : B' → B) (g' : S' → B')
  ( c : cocone f g X)
  ( up-c : universal-property-pushout f g c)
  ( coh : coherence-square-maps g' i j g)
  where

  universal-property-pushout-top-extended-by-equivalences :
    is-equiv i → is-equiv j →
    universal-property-pushout
      ( f ∘ i)
      ( g')
      ( cocone-comp-vertical' i g' j g f c coh)
  universal-property-pushout-top-extended-by-equivalences ie je =
    universal-property-pushout-rectangle-universal-property-pushout-top i g' f
      ( g , j , coh)
      ( c)
      ( universal-property-pushout-is-equiv i g' (g , j , coh) ie je)
      ( up-c)

  universal-property-pushout-top-extension-by-equivalences :
    {l : Level} → is-equiv i → is-equiv j →
    Σ (cocone (f ∘ i) g' X) (universal-property-pushout-Level l (f ∘ i) g')
  pr1 (universal-property-pushout-top-extension-by-equivalences ie je) =
    cocone-comp-vertical' i g' j g f c coh
  pr2 (universal-property-pushout-top-extension-by-equivalences ie je) =
    universal-property-pushout-top-extended-by-equivalences ie je
```

### Extending pushouts by equivalences of cocones

Given a commutative diagram where `i`, `j` and `k` are equivalences,

```text
           g'
       S' ---> B'
      / \       \
  f' /   \ k     \ j
    /     ∨   g   ∨
   A'     S ----> B
     \    |       |
    i \   | f     |
       \  ∨     ⌜ ∨
        > A ----> X
```

the induced square is a pushout:

```text
  S' ---> B'
  |       |
  |       |
  ∨     ⌜ ∨
  A' ---> X.
```

This combines both special cases of the pushout pasting lemmas for equivalences.

Notice that the triple `(i,j,k)` is really an equivalence of spans. Thus, this
result can be phrased as: the pushout is invariant under equivalence of spans.

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { S' : UU l5} {A' : UU l6} {B' : UU l7}
  ( f : S → A) (g : S → B) (f' : S' → A') (g' : S' → B')
  ( i : A' → A) (j : B' → B) (k : S' → S)
  ( c : cocone f g X)
  ( up-c : universal-property-pushout f g c)
  ( coh-l : coherence-square-maps k f' f i)
  ( coh-r : coherence-square-maps g' k j g)
  where

  universal-property-pushout-extension-by-equivalences :
    {l : Level} → is-equiv i → is-equiv j → is-equiv k →
    Σ (cocone f' g' X) (universal-property-pushout-Level l f' g')
  universal-property-pushout-extension-by-equivalences ie je ke =
    universal-property-pushout-top-extension-by-equivalences
      ( f')
      ( g ∘ k)
      ( id)
      ( j)
      ( g')
      ( cocone-comp-horizontal' f' k g f i c coh-l)
      ( universal-property-pushout-left-extended-by-equivalences f g k i
        ( f')
        ( c)
        ( up-c)
        ( coh-l)
        ( ke)
        ( ie))
      ( coh-r)
      ( is-equiv-id)
      ( je)

  universal-property-pushout-extended-by-equivalences :
    is-equiv i → is-equiv j → is-equiv k →
    universal-property-pushout
      ( f')
      ( g')
      ( comp-cocone-hom-span f g f' g' i j k c coh-l coh-r)
  universal-property-pushout-extended-by-equivalences ie je ke =
    pr2 (universal-property-pushout-extension-by-equivalences ie je ke)
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pushout if and only if the top square is a pushout

```agda
module _
  { l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  ( f : A → B) (g : A → C) (h : B → D) (k : C → D)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  ( f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  ( hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  ( top : coherence-square-maps g' f' k' h')
  ( back-left : coherence-square-maps f' hA hB f)
  ( back-right : coherence-square-maps g' hA hC g)
  ( front-left : coherence-square-maps h' hB hD h)
  ( front-right : coherence-square-maps k' hC hD k)
  ( bottom : coherence-square-maps g f k h)
  ( c :
    coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
      ( top)
      ( back-left)
      ( back-right)
      ( front-left)
      ( front-right)
      ( bottom))
  ( is-equiv-hA : is-equiv hA) (is-equiv-hB : is-equiv hB)
  ( is-equiv-hC : is-equiv hC) (is-equiv-hD : is-equiv hD)
  where

  universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv :
    universal-property-pushout f g (h , k , bottom) →
    universal-property-pushout f' g' (h' , k' , top)
  universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv
    ( up-bottom)
    { l = l} =
    universal-property-pushout-pullback-property-pushout f' g'
      ( h' , k' , top)
      ( λ W →
        is-pullback-bottom-is-pullback-top-cube-is-equiv
          ( precomp h' W)
          ( precomp k' W)
          ( precomp f' W)
          ( precomp g' W)
          ( precomp h W)
          ( precomp k W)
          ( precomp f W)
          ( precomp g W)
          ( precomp hD W)
          ( precomp hB W)
          ( precomp hC W)
          ( precomp hA W)
          ( precomp-coherence-square-maps g f k h bottom W)
          ( precomp-coherence-square-maps hB h' h hD (inv-htpy front-left) W)
          ( precomp-coherence-square-maps hC k' k hD (inv-htpy front-right) W)
          ( precomp-coherence-square-maps hA f' f hB (inv-htpy back-left) W)
          ( precomp-coherence-square-maps hA g' g hC (inv-htpy back-right) W)
          ( precomp-coherence-square-maps g' f' k' h' top W)
          ( precomp-coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
            ( top)
            ( back-left)
            ( back-right)
            ( front-left)
            ( front-right)
            ( bottom)
            ( c)
            ( W))
          ( is-equiv-precomp-is-equiv hD is-equiv-hD W)
          ( is-equiv-precomp-is-equiv hB is-equiv-hB W)
          ( is-equiv-precomp-is-equiv hC is-equiv-hC W)
          ( is-equiv-precomp-is-equiv hA is-equiv-hA W)
          ( pullback-property-pushout-universal-property-pushout f g
            ( h , k , bottom)
            ( up-bottom)
            ( W)))

  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv :
    universal-property-pushout f' g' (h' , k' , top) →
    universal-property-pushout f g (h , k , bottom)
  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
    ( up-top)
    { l = l} =
    universal-property-pushout-pullback-property-pushout f g
      ( h , k , bottom)
      ( λ W →
        is-pullback-top-is-pullback-bottom-cube-is-equiv
          ( precomp h' W)
          ( precomp k' W)
          ( precomp f' W)
          ( precomp g' W)
          ( precomp h W)
          ( precomp k W)
          ( precomp f W)
          ( precomp g W)
          ( precomp hD W)
          ( precomp hB W)
          ( precomp hC W)
          ( precomp hA W)
          ( precomp-coherence-square-maps g f k h bottom W)
          ( precomp-coherence-square-maps hB h' h hD (inv-htpy front-left) W)
          ( precomp-coherence-square-maps hC k' k hD (inv-htpy front-right) W)
          ( precomp-coherence-square-maps hA f' f hB (inv-htpy back-left) W)
          ( precomp-coherence-square-maps hA g' g hC (inv-htpy back-right) W)
          ( precomp-coherence-square-maps g' f' k' h' top W)
          ( precomp-coherence-cube-maps f g h k f' g' h' k' hA hB hC hD
            ( top)
            ( back-left)
            ( back-right)
            ( front-left)
            ( front-right)
            ( bottom)
            ( c)
            ( W))
          ( is-equiv-precomp-is-equiv hD is-equiv-hD W)
          ( is-equiv-precomp-is-equiv hB is-equiv-hB W)
          ( is-equiv-precomp-is-equiv hC is-equiv-hC W)
          ( is-equiv-precomp-is-equiv hA is-equiv-hA W)
          ( pullback-property-pushout-universal-property-pushout f' g'
            ( h' , k' , top)
            ( up-top)
            ( W)))

module _
  { l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  ( f : A → B) (g : A → C) (h : B → D) (k : C → D)
  { A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  ( f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  ( hA : A' ≃ A) (hB : B' ≃ B) (hC : C' ≃ C) (hD : D' ≃ D)
  ( top : coherence-square-maps g' f' k' h')
  ( back-left : coherence-square-maps f' (map-equiv hA) (map-equiv hB) f)
  ( back-right : coherence-square-maps g' (map-equiv hA) (map-equiv hC) g)
  ( front-left : coherence-square-maps h' (map-equiv hB) (map-equiv hD) h)
  ( front-right : coherence-square-maps k' (map-equiv hC) (map-equiv hD) k)
  ( bottom : coherence-square-maps g f k h)
  ( c :
    coherence-cube-maps f g h k f' g' h' k'
      ( map-equiv hA)
      ( map-equiv hB)
      ( map-equiv hC)
      ( map-equiv hD)
      ( top)
      ( back-left)
      ( back-right)
      ( front-left)
      ( front-right)
      ( bottom))
  where

  universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv :
    universal-property-pushout f g (h , k , bottom) →
    universal-property-pushout f' g' (h' , k' , top)
  universal-property-pushout-top-universal-property-pushout-bottom-cube-equiv =
    universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv
      f g h k f' g' h' k'
      ( map-equiv hA)
      ( map-equiv hB)
      ( map-equiv hC)
      ( map-equiv hD)
      ( top)
      ( back-left)
      ( back-right)
      ( front-left)
      ( front-right)
      ( bottom)
      ( c)
      ( is-equiv-map-equiv hA)
      ( is-equiv-map-equiv hB)
      ( is-equiv-map-equiv hC)
      ( is-equiv-map-equiv hD)

  universal-property-pushout-bottom-universal-property-pushout-top-cube-equiv :
    universal-property-pushout f' g' (h' , k' , top) →
    universal-property-pushout f g (h , k , bottom)
  universal-property-pushout-bottom-universal-property-pushout-top-cube-equiv =
    universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
      f g h k f' g' h' k'
      ( map-equiv hA)
      ( map-equiv hB)
      ( map-equiv hC)
      ( map-equiv hD)
      ( top)
      ( back-left)
      ( back-right)
      ( front-left)
      ( front-right)
      ( bottom)
      ( c)
      ( is-equiv-map-equiv hA)
      ( is-equiv-map-equiv hB)
      ( is-equiv-map-equiv hC)
      ( is-equiv-map-equiv hD)
```
