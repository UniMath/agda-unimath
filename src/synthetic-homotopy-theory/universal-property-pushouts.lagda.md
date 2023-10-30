# The universal property of pushouts

```agda
module synthetic-homotopy-theory.universal-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.spans
open import foundation.subtype-identity-principle
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies

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
  (X → Y) → cocone-span 𝒮 Y.
```

There are several ways of asserting a condition equivalent to the universal
property of pushouts:

1. The universal property of pushouts
2. The
   [pullback property of pushouts](synthetic-homotopy-theory.pullback-property-pushouts.md).
   This is a restatement of the universal property of pushouts in terms of
   pullbacks.
3. The
   [dependent universal property of pushouts](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).
   This property characterizes _dependent_ functions out of a pushout
4. The
   [dependent pullback property of pushouts](synthetic-homotopy-theory.dependent-pullback-property-pushouts.md).
   This is a restatement of the dependent universal property of pushouts in
   terms of pullbacks
5. The
   [induction principle of pushouts](synthetic-homotopy-theory.induction-principle-pushouts.md).
   This weaker form of the dependent universal property of pushouts expresses
   the induction principle of pushouts seen as higher inductive types.

## Definition

### The universal property of pushouts

```agda
universal-property-pushout :
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4} →
  cocone-span s X → UUω
universal-property-pushout s c =
  {l : Level} (Y : UU l) → is-equiv (cocone-span-map s {Y = Y} c)

module _
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {X : UU l4} {Y : UU l5} (c : cocone-span s X)
  (up-c : universal-property-pushout s c)
  (d : cocone-span s Y)
  where

  map-universal-property-pushout : X → Y
  map-universal-property-pushout = map-inv-is-equiv (up-c Y) d

  htpy-cocone-span-map-universal-property-pushout :
    htpy-cocone-span s (cocone-span-map s c map-universal-property-pushout) d
  htpy-cocone-span-map-universal-property-pushout =
    htpy-eq-cocone-span
      ( s)
      ( cocone-span-map s c map-universal-property-pushout)
      ( d)
      ( is-section-map-inv-is-equiv (up-c Y) d)

  horizontal-htpy-cocone-span-map-universal-property-pushout :
    map-universal-property-pushout ∘ horizontal-map-cocone-span s c ~
    horizontal-map-cocone-span s d
  horizontal-htpy-cocone-span-map-universal-property-pushout =
    horizontal-htpy-cocone-span
      ( s)
      ( cocone-span-map s c map-universal-property-pushout)
      ( d)
      ( htpy-cocone-span-map-universal-property-pushout)

  vertical-htpy-cocone-span-map-universal-property-pushout :
    map-universal-property-pushout ∘ vertical-map-cocone-span s c ~
    vertical-map-cocone-span s d
  vertical-htpy-cocone-span-map-universal-property-pushout =
    vertical-htpy-cocone-span
      ( s)
      ( cocone-span-map s c map-universal-property-pushout)
      ( d)
      ( htpy-cocone-span-map-universal-property-pushout)

  coherence-htpy-cocone-span-map-universal-property-pushout :
    statement-coherence-htpy-cocone-span s
      ( cocone-span-map s c map-universal-property-pushout)
      ( d)
      ( horizontal-htpy-cocone-span-map-universal-property-pushout)
      ( vertical-htpy-cocone-span-map-universal-property-pushout)
  coherence-htpy-cocone-span-map-universal-property-pushout =
    coherence-htpy-cocone-span
      ( s)
      ( cocone-span-map s c map-universal-property-pushout)
      ( d)
      ( htpy-cocone-span-map-universal-property-pushout)

  uniqueness-map-universal-property-pushout :
    is-contr ( Σ (X → Y) (λ h → htpy-cocone-span s (cocone-span-map s c h) d))
  uniqueness-map-universal-property-pushout =
    is-contr-is-equiv'
      ( fiber (cocone-span-map s c) d)
      ( tot (λ h → htpy-eq-cocone-span s (cocone-span-map s c h) d))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → is-equiv-htpy-eq-cocone-span s (cocone-span-map s c h) d))
      ( is-contr-map-is-equiv (up-c Y) d)
```

## Properties

### The 3-for-2 property of pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {X : UU l4} {Y : UU l5} (c : cocone-span s X) (d : cocone-span s Y)
  ( h : X → Y) (KLM : htpy-cocone-span s (cocone-span-map s c h) d)
  where

  triangle-map-cocone-span :
    { l6 : Level} (Z : UU l6) →
    ( cocone-span-map s d) ~ (cocone-span-map s c ∘ precomp h Z)
  triangle-map-cocone-span Z k =
    inv
      ( ( cocone-span-map-comp s c h k) ∙
        ( ap
          ( λ t → cocone-span-map s t k)
          ( eq-htpy-cocone-span s (cocone-span-map s c h) d KLM)))

  is-equiv-up-pushout-up-pushout :
    ( up-c : universal-property-pushout s c) →
    ( up-d : universal-property-pushout s d) →
    is-equiv h
  is-equiv-up-pushout-up-pushout up-c up-d =
    is-equiv-is-equiv-precomp h
      ( λ l Z →
        is-equiv-right-factor-htpy
          ( cocone-span-map s d)
          ( cocone-span-map s c)
          ( precomp h Z)
          ( triangle-map-cocone-span Z)
          ( up-c Z)
          ( up-d Z))

  up-pushout-up-pushout-is-equiv :
    is-equiv h → universal-property-pushout s c → universal-property-pushout s d
  up-pushout-up-pushout-is-equiv is-equiv-h up-c Z =
    is-equiv-comp-htpy
      ( cocone-span-map s d)
      ( cocone-span-map s c)
      ( precomp h Z)
      ( triangle-map-cocone-span Z)
      ( is-equiv-precomp-is-equiv h is-equiv-h Z)
      ( up-c Z)

  up-pushout-is-equiv-up-pushout :
    universal-property-pushout s d → is-equiv h → universal-property-pushout s c
  up-pushout-is-equiv-up-pushout up-d is-equiv-h Z =
    is-equiv-left-factor-htpy
      ( cocone-span-map s d)
      ( cocone-span-map s c)
      ( precomp h Z)
      ( triangle-map-cocone-span Z)
      ( up-d Z)
      ( is-equiv-precomp-is-equiv h is-equiv-h Z)
```

### Pushouts are uniquely unique

```agda
uniquely-unique-pushout :
  { l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  { X : UU l4} {Y : UU l5} (c : cocone-span s X) (d : cocone-span s Y) →
  universal-property-pushout s c →
  universal-property-pushout s d →
  is-contr
    ( Σ ( X ≃ Y)
        ( λ e → htpy-cocone-span s (cocone-span-map s c (map-equiv e)) d))
uniquely-unique-pushout s c d up-c up-d =
  is-torsorial-Eq-subtype
    ( uniqueness-map-universal-property-pushout s c up-c d)
    ( is-property-is-equiv)
    ( map-universal-property-pushout s c up-c d)
    ( htpy-cocone-span-map-universal-property-pushout s c up-c d)
    ( is-equiv-up-pushout-up-pushout s c d
      ( map-universal-property-pushout s c up-c d)
      ( htpy-cocone-span-map-universal-property-pushout s c up-c d)
      ( up-c)
      ( up-d))
```

### The universal property of pushouts is equivalent to the pullback property of pushouts

In order to show that the universal property of pushouts is equivalent to the
pullback property, we show that the maps `cocone-span-map` and the gap map fit in a
commuting triangle, where the third map is an equivalence. The claim then
follows from the 3-for-2 property of equivalences.

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4} (c : cocone-span s X)
  where
  
  triangle-pullback-property-pushout-universal-property-pushout :
    {l : Level} (Y : UU l) →
    cocone-span-map s c ~
    ( tot (λ i' → tot (λ j' → htpy-eq)) ∘
      gap
        ( _∘ left-map-span s)
        ( _∘ right-map-span s)
        ( cone-pullback-property-pushout s c Y))
  triangle-pullback-property-pushout-universal-property-pushout Y h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( inv (is-section-eq-htpy (h ·l coherence-square-cocone-span s c))))

  pullback-property-pushout-universal-property-pushout :
    universal-property-pushout s c → pullback-property-pushout s c
  pullback-property-pushout-universal-property-pushout up-c Y =
    is-equiv-right-factor-htpy
      ( cocone-span-map s c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span s)
        ( _∘ right-map-span s)
        ( cone-pullback-property-pushout s c Y))
      ( triangle-pullback-property-pushout-universal-property-pushout Y)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ i' →
          is-equiv-tot-is-fiberwise-equiv
            ( λ j' → funext (i' ∘ left-map-span s) (j' ∘ right-map-span s))))
      ( up-c Y)

  universal-property-pushout-pullback-property-pushout :
    pullback-property-pushout s c → universal-property-pushout s c
  universal-property-pushout-pullback-property-pushout pb-c Y =
    is-equiv-comp-htpy
      ( cocone-span-map s c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span s)
        ( _∘ right-map-span s)
        ( cone-pullback-property-pushout s c Y))
      ( triangle-pullback-property-pushout-universal-property-pushout Y)
      ( pb-c Y)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ i' →
          is-equiv-tot-is-fiberwise-equiv
            ( λ j' → funext (i' ∘ left-map-span s) (j' ∘ right-map-span s))))
```

### If the left map of a span is an equivalence, then the vertical map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {C : UU l4} (c : cocone-span s C)
  where

  is-equiv-universal-property-pushout :
    is-equiv (left-map-span s) →
    universal-property-pushout s c → is-equiv (vertical-map-cocone-span s c)
  is-equiv-universal-property-pushout is-equiv-f up-c =
    is-equiv-is-equiv-precomp
      ( vertical-map-cocone-span s c)
      ( λ l T →
        is-equiv-is-pullback'
          ( _∘ left-map-span s)
          ( _∘ right-map-span s)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (left-map-span s) is-equiv-f T)
          ( pullback-property-pushout-universal-property-pushout s c up-c T))

  universal-property-pushout-is-equiv :
    is-equiv (left-map-span s) → is-equiv (vertical-map-cocone-span s c) →
    universal-property-pushout s c
  universal-property-pushout-is-equiv H K =
    universal-property-pushout-pullback-property-pushout s c
      ( λ T →
        is-pullback-is-equiv'
          ( _∘ left-map-span s)
          ( _∘ right-map-span s)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (left-map-span s) H T)
          ( is-equiv-precomp-is-equiv (vertical-map-cocone-span s c) K T))

equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (e : S ≃ A) (g : S → B) (c : cocone-span (make-span (map-equiv e) g) C) →
  universal-property-pushout (make-span (map-equiv e) g) c →
  B ≃ C
pr1 (equiv-universal-property-pushout e g c up-c) =
  vertical-map-cocone-span (make-span (map-equiv e) g) c
pr2 (equiv-universal-property-pushout e g c up-c) =
  is-equiv-universal-property-pushout
    ( make-span (map-equiv e) g)
    ( c)
    ( is-equiv-map-equiv e)
    ( up-c)
```

### If the right map of a span is an equivalence, then the horizontal map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {C : UU l4} (c : cocone-span s C)
  where
  
  is-equiv-universal-property-pushout' :
    is-equiv (right-map-span s) →
    universal-property-pushout s c →
    is-equiv (horizontal-map-cocone-span s c)
  is-equiv-universal-property-pushout' is-equiv-g up-c =
    is-equiv-is-equiv-precomp
      ( horizontal-map-cocone-span s c)
      ( λ l T →
        is-equiv-is-pullback
          ( precomp (left-map-span s) T)
          ( precomp (right-map-span s) T)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (right-map-span s) is-equiv-g T)
          ( pullback-property-pushout-universal-property-pushout s c up-c T))

  universal-property-pushout-is-equiv' :
    is-equiv (right-map-span s) → is-equiv (horizontal-map-cocone-span s c) →
    universal-property-pushout s c
  universal-property-pushout-is-equiv' H K =
    universal-property-pushout-pullback-property-pushout s c
      ( λ T →
        is-pullback-is-equiv
          ( precomp (left-map-span s) T)
          ( precomp (right-map-span s) T)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (right-map-span s) H T)
          ( is-equiv-precomp-is-equiv (horizontal-map-cocone-span s c) K T))

equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (e : S ≃ B) (c : cocone-span (make-span f (map-equiv e)) C) →
  universal-property-pushout (make-span f (map-equiv e)) c →
  A ≃ C
pr1 (equiv-universal-property-pushout' f e c up-c) = pr1 c
pr2 (equiv-universal-property-pushout' f e c up-c) =
  is-equiv-universal-property-pushout'
    ( make-span f (map-equiv e))
    ( c)
    ( is-equiv-map-equiv e)
    ( up-c)
```

### The pushout pasting lemmas

#### The horizontal pushout pasting lemma

If in the following diagram the left square is a pushout, then the outer
rectangle is a pushout if and only if the right square is a pushout.

```text
      g       h
   S ----> B ----> C
   |       |       |
  f|       |       |
   v       v       v
   A ----> X ----> Y
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  { C : UU l4} {X : UU l5} {Y : UU l6}
  ( h : codomain-span s → C)
  ( c : cocone-span s X)
  ( d : cocone-span (make-span (vertical-map-cocone-span s c) h) Y)
  ( up-c : universal-property-pushout s c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-right :
    universal-property-pushout
      ( make-span (vertical-map-cocone-span s c) h)
      ( d) →
    universal-property-pushout
      ( right-extend-span s h)
      ( horizontal-comp-cocone-span s h c d)
  universal-property-pushout-rectangle-universal-property-pushout-right
    ( up-d)
    { l} =
    universal-property-pushout-pullback-property-pushout
      ( right-extend-span s h)
      ( horizontal-comp-cocone-span s h c d)
      ( λ W →
        tr
          ( is-pullback
            ( precomp (left-map-span s) W)
            ( precomp (h ∘ right-map-span s) W))
          ( inv
            ( eq-htpy-cone
              ( precomp (left-map-span s) W)
              ( precomp (h ∘ right-map-span s) W)
              ( cone-pullback-property-pushout
                ( right-extend-span s h)
                ( horizontal-comp-cocone-span s h c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp (left-map-span s) W)
                ( precomp (right-map-span s) W)
                ( precomp h W)
                ( cone-pullback-property-pushout s c W)
                ( cone-pullback-property-pushout
                  ( make-span (vertical-map-cocone-span s c) h)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( right-map-span s)
                  ( h)
                  ( left-map-span s)
                  ( vertical-map-cocone-span s c)
                  ( vertical-map-cocone-span
                    ( make-span (vertical-map-cocone-span s c) h)
                    ( d))
                  ( horizontal-map-cocone-span s c)
                  ( horizontal-map-cocone-span
                    ( make-span (vertical-map-cocone-span s c) h)
                    ( d))
                  ( coherence-square-cocone-span s c)
                  ( coherence-square-cocone-span
                    ( make-span (vertical-map-cocone-span s c) h)
                    ( d))))))
          ( is-pullback-rectangle-is-pullback-top
            ( precomp (left-map-span s) W)
            ( precomp (right-map-span s) W)
            ( precomp h W)
            ( cone-pullback-property-pushout s c W)
            ( cone-pullback-property-pushout
              ( make-span (vertical-map-cocone-span s c) h)
              ( d)
              ( W))
            ( pullback-property-pushout-universal-property-pushout s c
              ( up-c)
              ( W))
            ( pullback-property-pushout-universal-property-pushout
              ( make-span (vertical-map-cocone-span s c) h)
              ( d)
              ( up-d)
              ( W))))

  universal-property-pushout-right-universal-property-pushout-rectangle :
    universal-property-pushout
      ( right-extend-span s h)
      ( horizontal-comp-cocone-span s h c d) →
    universal-property-pushout
      ( make-span (vertical-map-cocone-span s c) h)
      ( d)
  universal-property-pushout-right-universal-property-pushout-rectangle
    ( up-r)
    { l} =
    universal-property-pushout-pullback-property-pushout
      ( make-span (vertical-map-cocone-span s c) h)
      ( d)
      ( λ W →
        is-pullback-top-is-pullback-rectangle
          ( precomp (left-map-span s) W)
          ( precomp (right-map-span s) W)
          ( precomp h W)
          ( cone-pullback-property-pushout s c W)
          ( cone-pullback-property-pushout
            ( make-span (vertical-map-cocone-span s c) h)
            ( d)
            ( W))
          ( pullback-property-pushout-universal-property-pushout s c
            ( up-c)
            ( W))
          ( tr
            ( is-pullback
              ( precomp (left-map-span s) W)
              ( precomp (h ∘ (right-map-span s)) W))
            ( eq-htpy-cone
              ( precomp (left-map-span s) W)
              ( precomp (h ∘ right-map-span s) W)
              ( cone-pullback-property-pushout
                ( right-extend-span s h)
                ( horizontal-comp-cocone-span s h c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp (left-map-span s) W)
                ( precomp (right-map-span s) W)
                ( precomp h W)
                ( cone-pullback-property-pushout s c W)
                ( cone-pullback-property-pushout
                  ( make-span (vertical-map-cocone-span s c) h)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( right-map-span s)
                  ( h)
                  ( left-map-span s)
                  ( vertical-map-cocone-span s c)
                  ( vertical-map-cocone-span
                    ( make-span (vertical-map-cocone-span s c) h)
                    ( d))
                  ( horizontal-map-cocone-span s c)
                  ( horizontal-map-cocone-span
                    ( make-span (vertical-map-cocone-span s c) h)
                    ( d))
                  ( coherence-square-cocone-span s c)
                  ( coherence-square-cocone-span
                    ( make-span (vertical-map-cocone-span s c) h)
                    ( d)))))
            ( pullback-property-pushout-universal-property-pushout
              ( right-extend-span s h)
              ( horizontal-comp-cocone-span s h c d)
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
   v   ≃   v    ⌜  v
   A' ---> A ----> X
       j
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {S' : UU l5} {A' : UU l6}
  ( f : S → A) (g : S → B) (i : S' → S) (j : A' → A) (f' : S' → A')
  ( c : cocone-span f g X)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  ( coh : coherence-square-maps i f' f j)
  where

  universal-property-pushout-left-extended-by-equivalences :
    is-equiv i → is-equiv j →
    {l : Level} →
    universal-property-pushout l
      ( f')
      ( g ∘ i)
      ( horizontal-comp-cocone-span' f' i g f j c coh)
  universal-property-pushout-left-extended-by-equivalences ie je =
    universal-property-pushout-rectangle-universal-property-pushout-right f' i g
      ( j , f , coh)
      ( c)
      ( universal-property-pushout-is-equiv' f' i (j , f , coh) ie je)
      ( up-c)
```

#### The vertical pushout pasting lemma

If in the following diagram the top square is a pushout, then the outer
rectangle is a pushout if and only if the bottom square is a pushout.

```text
       g
   A -----> X
   |        |
  f|        |
   v        v
   B -----> Y
   |        |
  k|        |
   v        v
   C -----> Z
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  ( f : A → B) (g : A → X) (k : B → C)
  ( c : cocone-span f g Y) (d : cocone-span k (horizontal-map-cocone-span f g c) Z)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-top :
    ( {l : Level} →
      universal-property-pushout l k (horizontal-map-cocone-span f g c) d) →
    ( {l : Level} →
      universal-property-pushout l (k ∘ f) g (vertical-comp-cocone-span f g k c d))
  universal-property-pushout-rectangle-universal-property-pushout-top
    ( up-d)
    { l} =
    universal-property-pushout-pullback-property-pushout l
      ( k ∘ f)
      ( g)
      ( vertical-comp-cocone-span f g k c d)
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
                ( vertical-comp-cocone-span f g k c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp k W)
                ( precomp f W)
                ( precomp g W)
                ( cone-pullback-property-pushout f g c W)
                ( cone-pullback-property-pushout k
                  ( horizontal-map-cocone-span f g c)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( g)
                  ( f)
                  ( vertical-map-cocone-span f g c)
                  ( horizontal-map-cocone-span f g c)
                  ( k)
                  ( vertical-map-cocone-span k (horizontal-map-cocone-span f g c) d)
                  ( horizontal-map-cocone-span k (horizontal-map-cocone-span f g c) d)
                  ( coherence-square-cocone-span f g c)
                  ( coherence-square-cocone-span k
                    ( horizontal-map-cocone-span f g c)
                    ( d))))))
          ( is-pullback-rectangle-is-pullback-left-square
            ( precomp k W)
            ( precomp f W)
            ( precomp g W)
            ( cone-pullback-property-pushout f g c W)
            ( cone-pullback-property-pushout k
              ( horizontal-map-cocone-span f g c)
              ( d)
              ( W))
            ( pullback-property-pushout-universal-property-pushout l f g c
              ( up-c)
              ( W))
            ( pullback-property-pushout-universal-property-pushout l k
              ( horizontal-map-cocone-span f g c)
              ( d)
              ( up-d)
              ( W))))

  universal-property-pushout-top-universal-property-pushout-rectangle :
    ( {l : Level} →
      universal-property-pushout l (k ∘ f) g (vertical-comp-cocone-span f g k c d)) →
    ( {l : Level} →
      universal-property-pushout l k (horizontal-map-cocone-span f g c) d)
  universal-property-pushout-top-universal-property-pushout-rectangle
    ( up-r)
    { l} =
    universal-property-pushout-pullback-property-pushout l k
      ( horizontal-map-cocone-span f g c)
      ( d)
      ( λ W →
        is-pullback-left-square-is-pullback-rectangle
          ( precomp k W)
          ( precomp f W)
          ( precomp g W)
          ( cone-pullback-property-pushout f g c W)
          ( cone-pullback-property-pushout k (horizontal-map-cocone-span f g c) d W)
          ( pullback-property-pushout-universal-property-pushout l f g c up-c W)
          ( tr
            ( is-pullback (precomp (k ∘ f) W) (precomp g W))
            ( eq-htpy-cone
              ( precomp (k ∘ f) W)
              ( precomp g W)
              ( cone-pullback-property-pushout
                ( k ∘ f)
                ( g)
                ( vertical-comp-cocone-span f g k c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp k W)
                ( precomp f W)
                ( precomp g W)
                ( cone-pullback-property-pushout f g c W)
                ( cone-pullback-property-pushout k
                  ( horizontal-map-cocone-span f g c)
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( g)
                  ( f)
                  ( vertical-map-cocone-span f g c)
                  ( horizontal-map-cocone-span f g c)
                  ( k)
                  ( vertical-map-cocone-span k
                    ( horizontal-map-cocone-span f g c)
                    ( d))
                  ( horizontal-map-cocone-span k
                    ( horizontal-map-cocone-span f g c)
                    ( d))
                  ( coherence-square-cocone-span f g c)
                  ( coherence-square-cocone-span k
                    ( horizontal-map-cocone-span f g c)
                    ( d)))))
            ( pullback-property-pushout-universal-property-pushout l (k ∘ f) g
              ( vertical-comp-cocone-span f g k c d)
              ( up-r)
              ( W))))
```

#### Extending pushouts by equivalences at the top

If we have a pushout square on the right, equivalences S' ≃ S and B' ≃ B, and a
map g' : S' → B' making the top square commute, then the vertical rectangle is
again a pushout. This is a special case of the vertical pushout pasting lemma.

```text
           g'
       S' ---> B'
       |       |
     i | ≃   ≃ | j
       |       |
       v   g   v
       S ----> B
       |       |
     f |       |
       v    ⌜  v
       A ----> X
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {S' : UU l5} {B' : UU l6}
  ( f : S → A) (g : S → B) (i : S' → S) (j : B' → B) (g' : S' → B')
  ( c : cocone-span f g X)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  ( coh : coherence-square-maps g' i j g)
  where

  universal-property-pushout-top-extended-by-equivalences :
    is-equiv i → is-equiv j →
    {l : Level} →
    universal-property-pushout l
      ( f ∘ i)
      ( g')
      ( vertical-comp-cocone-span' i g' j g f c coh)
  universal-property-pushout-top-extended-by-equivalences ie je =
    universal-property-pushout-rectangle-universal-property-pushout-top i g' f
      ( g , j , coh)
      ( c)
      ( universal-property-pushout-is-equiv i g' (g , j , coh) ie je)
      ( up-c)
```

### Extending pushouts by equivalences of cocones

Given a commutative diagram where i, j and k are equivalences,

```text
          g'
      S' ---> B'
     / \       \
 f' /   \ k     \ j
   /     v   g   v
  A'     S ----> B
    \    |       |
   i \   | f     |
      \  v    ⌜  v
       > A ----> X
```

the induced square is a pushout.

```text
   S' ---> B'
   |       |
   |       |
   v       v
   A' ---> X
```

This combines both special cases of the pushout pasting lemmas for equivalences.

Notice that the triple (i.j.k) is really an equivalence of spans. Thus, this
result can be phrased as: the pushout is invariant under equivalence of spans.

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  { S' : UU l5} {A' : UU l6} {B' : UU l7}
  ( f : S → A) (g : S → B) (f' : S' → A') (g' : S' → B')
  ( i : A' → A) (j : B' → B) (k : S' → S)
  ( c : cocone-span f g X)
  ( up-c : {l : Level} → universal-property-pushout l f g c)
  ( coh-l : coherence-square-maps k f' f i)
  ( coh-r : coherence-square-maps g' k j g)
  where

  universal-property-pushout-extended-by-equivalences :
    is-equiv i → is-equiv j → is-equiv k →
    {l : Level} →
    universal-property-pushout l
      ( f')
      ( g')
      ( comp-cocone-span-hom-span f g f' g' i j k c coh-l coh-r)
  universal-property-pushout-extended-by-equivalences ie je ke =
    universal-property-pushout-top-extended-by-equivalences f'
      ( g ∘ k)
      ( id)
      ( j)
      ( g')
      ( horizontal-comp-cocone-span' f' k g f i c coh-l)
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
    ( {l : Level} →
      universal-property-pushout l f g (h , k , bottom)) →
    ( {l : Level} →
      universal-property-pushout l f' g' (h' , k' , top))
  universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv
    ( up-bottom)
    { l = l} =
    universal-property-pushout-pullback-property-pushout l f' g'
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
          ( pullback-property-pushout-universal-property-pushout l f g
            ( h , k , bottom)
            ( up-bottom)
            ( W)))

  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv :
    ( {l : Level} →
      universal-property-pushout l f' g' (h' , k' , top)) →
    ( {l : Level} →
      universal-property-pushout l f g (h , k , bottom))
  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equiv
    ( up-top)
    { l = l} =
    universal-property-pushout-pullback-property-pushout l f g
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
          ( pullback-property-pushout-universal-property-pushout l f' g'
            ( h' , k' , top)
            ( up-top)
            ( W)))
```
