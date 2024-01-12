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
open import foundation.commuting-triangles-of-maps
open import foundation.cones-over-cospans
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.equivalences-span-diagrams
open import foundation.extensions-span-diagrams
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-span-diagrams
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.span-diagrams
open import foundation.subtype-identity-principle
open import foundation.transport-along-identifications
open import foundation.transposition-span-diagrams
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-span-diagrams
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.pullback-property-pushouts
```

</details>

## Idea

Consider a [span diagram](foundation-core.span-diagrams.md) `𝒮` of types

```text
      f     g
  A <--- S ---> B.
```

and a type `X` equipped with a
[cocone structure](synthetic-homotopy-theory.cocones-under-span-diagrams.md) of
`S` into `X`. The **universal property of the pushout** of `𝒮` asserts that `X`
is the _initial_ type equipped with such cocone structure. In other words, the
universal property of the pushout of `𝒮` asserts that the following evaluation
map is an equivalence:

```text
  (X → Y) → cocone-span-diagram 𝒮 Y.
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

Examples of pushouts include
[suspensions](synthetic-homotopy-theory.suspensions-of-types.md),
[spheres](synthetic-homotopy-theory.spheres.md),
[joins](synthetic-homotopy-theory.joins-of-types.md), and the
[smash product](synthetic-homotopy-theory.smash-products-of-pointed-types.md).

## Definition

### The universal property of pushouts

```agda
universal-property-pushout :
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) {X : UU l4} → cocone-span-diagram s X → UUω
universal-property-pushout s c =
  {l : Level} (Y : UU l) → is-equiv (cocone-map-span-diagram s {Y = Y} c)

module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X) (H : universal-property-pushout s c)
  {Y : UU l5} (d : cocone-span-diagram s Y)
  where

  map-universal-property-pushout : X → Y
  map-universal-property-pushout = map-inv-is-equiv (H Y) d

  htpy-cocone-universal-property-pushout :
    htpy-cocone-span-diagram s
      ( cocone-map-span-diagram s c map-universal-property-pushout)
      ( d)
  htpy-cocone-universal-property-pushout =
    htpy-eq-cocone-span-diagram
      ( s)
      ( cocone-map-span-diagram s c map-universal-property-pushout)
      ( d)
      ( is-section-map-inv-is-equiv (H Y) d)

  cocone-map-universal-property-pushout : cocone-span-diagram s Y
  cocone-map-universal-property-pushout =
    cocone-map-span-diagram s c map-universal-property-pushout

  left-htpy-cocone-universal-property-pushout :
    coherence-triangle-maps'
      ( left-map-cocone-span-diagram s d)
      ( map-universal-property-pushout)
      ( left-map-cocone-span-diagram s c)
  left-htpy-cocone-universal-property-pushout =
    left-htpy-cocone-span-diagram
      ( s)
      ( cocone-map-universal-property-pushout)
      ( d)
      ( htpy-cocone-universal-property-pushout)

  right-htpy-cocone-universal-property-pushout :
    map-universal-property-pushout ∘ right-map-cocone-span-diagram s c ~
    right-map-cocone-span-diagram s d
  right-htpy-cocone-universal-property-pushout =
    right-htpy-cocone-span-diagram
      ( s)
      ( cocone-map-universal-property-pushout)
      ( d)
      ( htpy-cocone-universal-property-pushout)

  coherence-htpy-cocone-universal-property-pushout :
    statement-coherence-htpy-cocone-span-diagram s
      ( cocone-map-span-diagram s c map-universal-property-pushout)
      ( d)
      ( left-htpy-cocone-universal-property-pushout)
      ( right-htpy-cocone-universal-property-pushout)
  coherence-htpy-cocone-universal-property-pushout =
    coherence-htpy-cocone-span-diagram
      ( s)
      ( cocone-map-universal-property-pushout)
      ( d)
      ( htpy-cocone-universal-property-pushout)

  abstract
    uniqueness-map-universal-property-pushout :
      is-contr
        ( Σ ( X → Y)
            ( λ h →
              htpy-cocone-span-diagram s (cocone-map-span-diagram s c h) d))
    uniqueness-map-universal-property-pushout =
      is-contr-is-equiv'
        ( fiber (cocone-map-span-diagram s c) d)
        ( tot
          ( λ h →
            htpy-eq-cocone-span-diagram s (cocone-map-span-diagram s c h) d))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ h →
            is-equiv-htpy-eq-cocone-span-diagram s
              ( cocone-map-span-diagram s c h)
              ( d)))
        ( is-contr-map-is-equiv (H Y) d)
```

## Properties

### The 3-for-2 property of pushouts

The {{#concept "3-for-2 property of pushouts}} asserts that for any two cocones

```text
        g                g
    S -----> B       S -----> B
    |        |       |        |
  f |   H    | j   f |   H'   | j'
    V        V       V        V
    A -----> X       A -----> X'
        i                i'
```

and a map `h : X → X'` equipped with a homotopy of cocones

```text
  cocone-map-span-diagram s (i , j , H) h ~ (i' , j' , H'),
```

if any two of the following three conditions hold, then so does the third:

1. The cocone `(i , j , H)` satisfies the universal property of the pushout of
   `s`
2. The cocone `(i' , j' , H')` satisfies the universal property of the pushout
   of `s`
3. The map `h : X → X'` is an equivalence.

**Proof.** For any type `Y` there is a commuting triangle

```text
              - ∘ ĥ
     (X → Y) -------> (X' → Y)
            \        /
             \      /
              ∨    ∨
            cocone s Y
```

Thus we see that if both `(i , j , H)` and `(i' , j' , H')` satisfy the
universal property of pushouts, then `- ∘ h` is an equivalence for every type
`Y`, and this is equivalent to `h` being an equivalence. Conversely, if `h` is
an equivalence, then the left map in the above triangle is an equivalence if and
only if the right map is an equivalence, so it follows that `(i , j , H)` is
universal if and only if `(i' , j' , H')` is an equivalence.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  {X' : UU l5} (c' : cocone-span-diagram s X')
  (h : X → X') (H : htpy-cocone-span-diagram s (cocone-map-span-diagram s c h) c')
  where

  triangle-cocone-map-span-diagram :
    {l6 : Level} (Z : UU l6) →
    coherence-triangle-maps
      ( cocone-map-span-diagram s c')
      ( cocone-map-span-diagram s c)
      ( precomp h Z)
  triangle-cocone-map-span-diagram Z k =
    inv
      ( ( compute-comp-cocone-map-span-diagram s c h k) ∙
        ( ap
          ( λ t → cocone-map-span-diagram s t k)
          ( eq-htpy-cocone-span-diagram s
            ( cocone-map-span-diagram s c h)
            ( c')
            ( H))))

  abstract
    is-equiv-universal-property-pushout-universal-property-pushout :
      universal-property-pushout s c →
      universal-property-pushout s c' →
      is-equiv h
    is-equiv-universal-property-pushout-universal-property-pushout U V =
      is-equiv-is-equiv-precomp h
        ( λ Z →
          is-equiv-top-map-triangle
            ( cocone-map-span-diagram s c')
            ( cocone-map-span-diagram s c)
            ( precomp h Z)
            ( triangle-cocone-map-span-diagram Z)
            ( U Z)
            ( V Z))

  abstract
    universal-property-pushout-universal-property-pushout-is-equiv :
      is-equiv h →
      universal-property-pushout s c →
      universal-property-pushout s c'
    universal-property-pushout-universal-property-pushout-is-equiv K U Z =
      is-equiv-left-map-triangle
        ( cocone-map-span-diagram s c')
        ( cocone-map-span-diagram s c)
        ( precomp h Z)
        ( triangle-cocone-map-span-diagram Z)
        ( is-equiv-precomp-is-equiv h K Z)
        ( U Z)

  abstract
    universal-property-pushout-is-equiv-universal-property-pushout :
      universal-property-pushout s c' →
      is-equiv h →
      universal-property-pushout s c
    universal-property-pushout-is-equiv-universal-property-pushout U K Z =
      is-equiv-right-map-triangle
        ( cocone-map-span-diagram s c')
        ( cocone-map-span-diagram s c)
        ( precomp h Z)
        ( triangle-cocone-map-span-diagram Z)
        ( U Z)
        ( is-equiv-precomp-is-equiv h K Z)
```

### Pushouts are uniquely unique

Consider two cocones

```text
        g                g
    S -----> B       S -----> B
    |        |       |        |
  f |   H    | j   f |   H'   | j'
    V        V       V        V
    A -----> X       A -----> X'
        i                i'
```

on the same span diagram `s`, and assume that both `(i , j , H)` and (i' , j' ,
H')`satisfy the universal property of the pushout of`s`. Then the type of equivalences `e
: X ≃ X'` equipped with a homotopy of cocones

```text
  cocone-map-span-diagram s (i , j , H) (map-equiv e) ~ (i' , j' , H')
```

is contractible.

**Proof.** By the 3-for-2 property of pushouts it follows that every map
`h : X → X'` equipped with a homotopy of cocones

```text
  cocone-map-span-diagram s (i , j , H) h ~ (i' , j' , H'),
```

is an equivalence. Furthermore, the type of such maps is contractible by the
universal property of pushouts. Hence the claim follows.

```agda
abstract
  uniquely-unique-pushout :
    { l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
    { X : UU l4} (c : cocone-span-diagram s X)
    { Y : UU l5} (d : cocone-span-diagram s Y) →
    universal-property-pushout s c →
    universal-property-pushout s d →
    is-contr
      ( Σ ( X ≃ Y)
          ( λ e →
            htpy-cocone-span-diagram s
              ( cocone-map-span-diagram s c (map-equiv e))
              ( d)))
  uniquely-unique-pushout s c d H K =
    is-torsorial-Eq-subtype
      ( uniqueness-map-universal-property-pushout s c H d)
      ( is-property-is-equiv)
      ( map-universal-property-pushout s c H d)
      ( htpy-cocone-universal-property-pushout s c H d)
      ( is-equiv-universal-property-pushout-universal-property-pushout s c d
        ( map-universal-property-pushout s c H d)
        ( htpy-cocone-universal-property-pushout s c H d)
        ( H)
        ( K))
```

### The universal property of pushouts is equivalent to the pullback property of pushouts

**Proof.** Consider a cocone `c` with codomain `X` on a span diagram
`A <- S -> B` and a type `Y`. Then there is a commuting triangle

```text
  (X → Y) -----> (A → Y) ×_(S → Y) (B → Y)
         \      /
          \    / ≃
           ∨  ∨
        cocone s Y
```

in which the right map is an equivalence. Therefore it follows that the left map
is an equivalence if and only if the top map is an equivalence, from which we
conclude the theorem.

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  where

  triangle-pullback-property-pushout-universal-property-pushout :
    {l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( cocone-map-span-diagram s c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span-diagram s)
        ( _∘ right-map-span-diagram s)
        ( cone-pullback-property-pushout s c Y))
  triangle-pullback-property-pushout-universal-property-pushout Y h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( inv
          ( is-section-eq-htpy
            ( h ·l coherence-square-cocone-span-diagram s c))))

  pullback-property-pushout-universal-property-pushout :
    universal-property-pushout s c → pullback-property-pushout s c
  pullback-property-pushout-universal-property-pushout H Y =
    is-equiv-top-map-triangle
      ( cocone-map-span-diagram s c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span-diagram s)
        ( _∘ right-map-span-diagram s)
        ( cone-pullback-property-pushout s c Y))
      ( triangle-pullback-property-pushout-universal-property-pushout Y)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ i' →
          is-equiv-tot-is-fiberwise-equiv
            ( λ j' →
              funext
                ( i' ∘ left-map-span-diagram s)
                ( j' ∘ right-map-span-diagram s))))
      ( H Y)

  universal-property-pushout-pullback-property-pushout :
    pullback-property-pushout s c → universal-property-pushout s c
  universal-property-pushout-pullback-property-pushout pb-c Y =
    is-equiv-left-map-triangle
      ( cocone-map-span-diagram s c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span-diagram s)
        ( _∘ right-map-span-diagram s)
        ( cone-pullback-property-pushout s c Y))
      ( triangle-pullback-property-pushout-universal-property-pushout Y)
      ( pb-c Y)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ i' →
          is-equiv-tot-is-fiberwise-equiv
            ( λ j' →
              funext
                ( i' ∘ left-map-span-diagram s)
                ( j' ∘ right-map-span-diagram s))))
```

### If the left map of a span diagram is an equivalence, then the right map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  {C : UU l4} (c : cocone-span-diagram s C)
  where

  is-equiv-right-map-cocone-universal-property-pushout :
    is-equiv (left-map-span-diagram s) →
    universal-property-pushout s c →
    is-equiv (right-map-cocone-span-diagram s c)
  is-equiv-right-map-cocone-universal-property-pushout is-equiv-f H =
    is-equiv-is-equiv-precomp
      ( right-map-cocone-span-diagram s c)
      ( λ T →
        is-equiv-is-pullback'
          ( _∘ left-map-span-diagram s)
          ( _∘ right-map-span-diagram s)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (left-map-span-diagram s) is-equiv-f T)
          ( pullback-property-pushout-universal-property-pushout s c H T))

  universal-property-pushout-is-equiv :
    is-equiv (left-map-span-diagram s) →
    is-equiv (right-map-cocone-span-diagram s c) →
    universal-property-pushout s c
  universal-property-pushout-is-equiv H K =
    universal-property-pushout-pullback-property-pushout s c
      ( λ T →
        is-pullback-is-equiv'
          ( _∘ left-map-span-diagram s)
          ( _∘ right-map-span-diagram s)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (left-map-span-diagram s) H T)
          ( is-equiv-precomp-is-equiv (right-map-cocone-span-diagram s c) K T))

equiv-right-map-cocone-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (e : S ≃ A) (g : S → B)
  (c : cocone-span-diagram (make-span-diagram (map-equiv e) g) C) →
  universal-property-pushout (make-span-diagram (map-equiv e) g) c →
  B ≃ C
pr1 (equiv-right-map-cocone-universal-property-pushout e g c H) =
  right-map-cocone-span-diagram (make-span-diagram (map-equiv e) g) c
pr2 (equiv-right-map-cocone-universal-property-pushout e g c H) =
  is-equiv-right-map-cocone-universal-property-pushout
    ( make-span-diagram (map-equiv e) g)
    ( c)
    ( is-equiv-map-equiv e)
    ( H)
```

### If the right map of a span diagram is an equivalence, then the left map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  {C : UU l4} (c : cocone-span-diagram s C)
  where

  is-equiv-left-map-cocone-universal-property-pushout :
    is-equiv (right-map-span-diagram s) →
    universal-property-pushout s c →
    is-equiv (left-map-cocone-span-diagram s c)
  is-equiv-left-map-cocone-universal-property-pushout is-equiv-g H =
    is-equiv-is-equiv-precomp
      ( left-map-cocone-span-diagram s c)
      ( λ T →
        is-equiv-is-pullback
          ( precomp (left-map-span-diagram s) T)
          ( precomp (right-map-span-diagram s) T)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (right-map-span-diagram s) is-equiv-g T)
          ( pullback-property-pushout-universal-property-pushout s c H T))

  universal-property-pushout-is-equiv' :
    is-equiv (right-map-span-diagram s) →
    is-equiv (left-map-cocone-span-diagram s c) →
    universal-property-pushout s c
  universal-property-pushout-is-equiv' H K =
    universal-property-pushout-pullback-property-pushout s c
      ( λ T →
        is-pullback-is-equiv
          ( precomp (left-map-span-diagram s) T)
          ( precomp (right-map-span-diagram s) T)
          ( cone-pullback-property-pushout s c T)
          ( is-equiv-precomp-is-equiv (right-map-span-diagram s) H T)
          ( is-equiv-precomp-is-equiv (left-map-cocone-span-diagram s c) K T))

equiv-left-map-cocone-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (e : S ≃ B)
  (c : cocone-span-diagram (make-span-diagram f (map-equiv e)) C) →
  universal-property-pushout (make-span-diagram f (map-equiv e)) c →
  A ≃ C
pr1 (equiv-left-map-cocone-universal-property-pushout f e c H) =
  pr1 c
pr2 (equiv-left-map-cocone-universal-property-pushout f e c H) =
  is-equiv-left-map-cocone-universal-property-pushout
    ( make-span-diagram f (map-equiv e))
    ( c)
    ( is-equiv-map-equiv e)
    ( H)
```

### The pushout pasting lemmas

#### The horizontal pushout pasting lemma

The {{#concept "horizontal pushout pasting lemma"}} asserts that if in the left
square in the diagram

```text
       g       h
    S ----> B ----> C
    |       |       |
  f |       |       |
    v     ⌜ v       v
    A ----> X ----> Y
```

is a pushout, then the outer rectangle is a pushout if and only if the right
square is a pushout.

**Proof.** Consider a type `Z`. Then we obtain a commuting diagram

```text
              - ∘ g            - ∘ h
     (Y → Z) -------> (X → Z) -------> (A → Z)
        |                | ⌟              |
  - ∘ f |                |                |
        v                v                v
     (C → Z) -------> (B → Z) -------> (S → Z)
```

in which the right square is a pullback square. By the pasting lemma for
pullbacks it follows that the left square is a pullback square if and only if
the outer rectangle is a pullback square. The claim therefore follows by the
pullback property of pushouts.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6}
  (h : codomain-span-diagram s → C)
  (c : cocone-span-diagram s X)
  (d : cocone-span-diagram (make-span-diagram (right-map-cocone-span-diagram s c) h) Y)
  (H : universal-property-pushout s c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-right-square :
    universal-property-pushout
      ( make-span-diagram (right-map-cocone-span-diagram s c) h)
      ( d) →
    universal-property-pushout
      ( right-extend-span-diagram s h)
      ( horizontal-comp-cocone-span-diagram s h c d)
  universal-property-pushout-rectangle-universal-property-pushout-right-square
    U =
    universal-property-pushout-pullback-property-pushout
      ( right-extend-span-diagram s h)
      ( horizontal-comp-cocone-span-diagram s h c d)
      ( λ W →
        tr
          ( is-pullback
            ( precomp (left-map-span-diagram s) W)
            ( precomp (h ∘ right-map-span-diagram s) W))
          ( inv
            ( eq-htpy-cone
              ( precomp (left-map-span-diagram s) W)
              ( precomp (h ∘ right-map-span-diagram s) W)
              ( cone-pullback-property-pushout
                ( right-extend-span-diagram s h)
                ( horizontal-comp-cocone-span-diagram s h c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp (left-map-span-diagram s) W)
                ( precomp (right-map-span-diagram s) W)
                ( precomp h W)
                ( cone-pullback-property-pushout s c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                  ( d)
                  ( W)))
              ( ( refl-htpy) ,
                ( refl-htpy) ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( right-map-span-diagram s)
                  ( h)
                  ( left-map-span-diagram s)
                  ( right-map-cocone-span-diagram s c)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                    ( d))
                  ( left-map-cocone-span-diagram s c)
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                    ( d))
                  ( coherence-square-cocone-span-diagram s c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                    ( d))))))
          ( is-pullback-rectangle-is-pullback-top
            ( precomp (left-map-span-diagram s) W)
            ( precomp (right-map-span-diagram s) W)
            ( precomp h W)
            ( cone-pullback-property-pushout s c W)
            ( cone-pullback-property-pushout
              ( make-span-diagram (right-map-cocone-span-diagram s c) h)
              ( d)
              ( W))
            ( pullback-property-pushout-universal-property-pushout s c
              ( H)
              ( W))
            ( pullback-property-pushout-universal-property-pushout
              ( make-span-diagram (right-map-cocone-span-diagram s c) h)
              ( d)
              ( U)
              ( W))))

  universal-property-pushout-right-square-universal-property-pushout-rectangle :
    universal-property-pushout
      ( right-extend-span-diagram s h)
      ( horizontal-comp-cocone-span-diagram s h c d) →
    universal-property-pushout
      ( make-span-diagram (right-map-cocone-span-diagram s c) h)
      ( d)
  universal-property-pushout-right-square-universal-property-pushout-rectangle
    ( K)
    { l} =
    universal-property-pushout-pullback-property-pushout
      ( make-span-diagram (right-map-cocone-span-diagram s c) h)
      ( d)
      ( λ W →
        is-pullback-top-is-pullback-rectangle
          ( precomp (left-map-span-diagram s) W)
          ( precomp (right-map-span-diagram s) W)
          ( precomp h W)
          ( cone-pullback-property-pushout s c W)
          ( cone-pullback-property-pushout
            ( make-span-diagram (right-map-cocone-span-diagram s c) h)
            ( d)
            ( W))
          ( pullback-property-pushout-universal-property-pushout s c H W)
          ( tr
            ( is-pullback
              ( precomp (left-map-span-diagram s) W)
              ( precomp (h ∘ (right-map-span-diagram s)) W))
            ( eq-htpy-cone
              ( precomp (left-map-span-diagram s) W)
              ( precomp (h ∘ right-map-span-diagram s) W)
              ( cone-pullback-property-pushout
                ( right-extend-span-diagram s h)
                ( horizontal-comp-cocone-span-diagram s h c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp (left-map-span-diagram s) W)
                ( precomp (right-map-span-diagram s) W)
                ( precomp h W)
                ( cone-pullback-property-pushout s c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                  ( d)
                  ( W)))
              ( ( refl-htpy) ,
                ( refl-htpy) ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( right-map-span-diagram s)
                  ( h)
                  ( left-map-span-diagram s)
                  ( right-map-cocone-span-diagram s c)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                    ( d))
                  ( left-map-cocone-span-diagram s c)
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                    ( d))
                  ( coherence-square-cocone-span-diagram s c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram s c) h)
                    ( d)))))
            ( pullback-property-pushout-universal-property-pushout
              ( right-extend-span-diagram s h)
              ( horizontal-comp-cocone-span-diagram s h c d)
              ( K)
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
     v   ≃   v     ⌜ v
     A' ---> A ----> X
         j
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3) {X : UU l4}
  { S' : UU l5} {A' : UU l6} (f' : S' → A')
  ( e : equiv-arrow f' (left-map-span-diagram s))
  ( c : cocone-span-diagram s X)
  where

  universal-property-pushout-cocone-left-extend-equiv-arrow-span-diagram :
    universal-property-pushout s c →
    universal-property-pushout
      ( left-extend-equiv-arrow-span-diagram s f' e)
      ( cocone-left-extend-equiv-arrow-span-diagram s f' e c)
  universal-property-pushout-cocone-left-extend-equiv-arrow-span-diagram =
    universal-property-pushout-rectangle-universal-property-pushout-right-square
      ( span-diagram-equiv-arrow f' (left-map-span-diagram s) e)
      ( right-map-span-diagram s)
      ( cocone-equiv-arrow f' (left-map-span-diagram s) e)
      ( c)
      ( universal-property-pushout-is-equiv'
        ( span-diagram-equiv-arrow f' (left-map-span-diagram s) e)
        ( cocone-equiv-arrow f' (left-map-span-diagram s) e)
        ( is-equiv-map-domain-equiv-arrow f' (left-map-span-diagram s) e)
        ( is-equiv-map-codomain-equiv-arrow f' (left-map-span-diagram s) e))
```

#### The vertical pushout pasting lemma

If in the following diagram the top square is a pushout, then the outer
rectangle is a pushout if and only if the bottom square is a pushout.

```text
        g
    S -----> B
    |        |
  f |        |
    v      ⌜ v
    B -----> Y
    |        |
  h |        |
    v        v
    zC -----> Y
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  { C : UU l4} {X : UU l5} {Y : UU l6} (h : domain-span-diagram s → C)
  ( c : cocone-span-diagram s X)
  ( d : cocone-span-diagram (make-span-diagram h (left-map-cocone-span-diagram s c)) Y)
  ( H : universal-property-pushout s c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-top :
    ( universal-property-pushout
      ( make-span-diagram h (left-map-cocone-span-diagram s c))
      ( d)) →
    ( universal-property-pushout
      ( make-span-diagram
        ( h ∘ left-map-span-diagram s)
        ( right-map-span-diagram s))
      ( vertical-comp-cocone-span-diagram s h c d))
  universal-property-pushout-rectangle-universal-property-pushout-top U =
    universal-property-pushout-pullback-property-pushout
      ( make-span-diagram
        ( h ∘ left-map-span-diagram s)
        ( right-map-span-diagram s))
      ( vertical-comp-cocone-span-diagram s h c d)
      ( λ W →
        tr
          ( is-pullback
            ( precomp (h ∘ left-map-span-diagram s) W)
            ( precomp (right-map-span-diagram s) W))
          ( inv
            ( eq-htpy-cone
              ( precomp (h ∘ left-map-span-diagram s) W)
              ( precomp (right-map-span-diagram s) W)
              ( cone-pullback-property-pushout
                ( make-span-diagram
                  ( h ∘ left-map-span-diagram s)
                  ( right-map-span-diagram s))
                ( vertical-comp-cocone-span-diagram s h c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp h W)
                ( precomp (left-map-span-diagram s) W)
                ( precomp (right-map-span-diagram s) W)
                ( cone-pullback-property-pushout s c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram h (left-map-cocone-span-diagram s c))
                  ( d)
                  ( W)))
              ( ( refl-htpy) ,
                ( refl-htpy) ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( right-map-span-diagram s)
                  ( left-map-span-diagram s)
                  ( right-map-cocone-span-diagram s c)
                  ( left-map-cocone-span-diagram s c)
                  ( h)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram s c))
                    ( d))
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram s c))
                    ( d))
                  ( coherence-square-cocone-span-diagram s c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram s c))
                    ( d))))))
          ( is-pullback-rectangle-is-pullback-left-square
            ( precomp h W)
            ( precomp (left-map-span-diagram s) W)
            ( precomp (right-map-span-diagram s) W)
            ( cone-pullback-property-pushout s c W)
            ( cone-pullback-property-pushout
              ( make-span-diagram h (left-map-cocone-span-diagram s c))
              ( d)
              ( W))
            ( pullback-property-pushout-universal-property-pushout s c H W)
            ( pullback-property-pushout-universal-property-pushout
              ( make-span-diagram h (left-map-cocone-span-diagram s c))
              ( d)
              ( U)
              ( W))))

  universal-property-pushout-top-universal-property-pushout-rectangle :
    universal-property-pushout
      ( make-span-diagram
        ( h ∘ left-map-span-diagram s)
        ( right-map-span-diagram s))
      ( vertical-comp-cocone-span-diagram s h c d) →
    universal-property-pushout
      ( make-span-diagram h (left-map-cocone-span-diagram s c))
      ( d)
  universal-property-pushout-top-universal-property-pushout-rectangle U =
    universal-property-pushout-pullback-property-pushout
      ( make-span-diagram h (left-map-cocone-span-diagram s c))
      ( d)
      ( λ W →
        is-pullback-left-square-is-pullback-rectangle
          ( precomp h W)
          ( precomp (left-map-span-diagram s) W)
          ( precomp (right-map-span-diagram s) W)
          ( cone-pullback-property-pushout s c W)
          ( cone-pullback-property-pushout
            ( make-span-diagram h (left-map-cocone-span-diagram s c))
            ( d)
            ( W))
          ( pullback-property-pushout-universal-property-pushout s c H W)
          ( tr
            ( is-pullback
              ( precomp (h ∘ left-map-span-diagram s) W)
              ( precomp (right-map-span-diagram s) W))
            ( eq-htpy-cone
              ( precomp (h ∘ left-map-span-diagram s) W)
              ( precomp (right-map-span-diagram s) W)
              ( cone-pullback-property-pushout
                ( make-span-diagram
                  ( h ∘ left-map-span-diagram s)
                  ( right-map-span-diagram s))
                ( vertical-comp-cocone-span-diagram s h c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp h W)
                ( precomp (left-map-span-diagram s) W)
                ( precomp (right-map-span-diagram s) W)
                ( cone-pullback-property-pushout s c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram h (left-map-cocone-span-diagram s c))
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( right-map-span-diagram s)
                  ( left-map-span-diagram s)
                  ( right-map-cocone-span-diagram s c)
                  ( left-map-cocone-span-diagram s c)
                  ( h)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram s c))
                    ( d))
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram s c))
                    ( d))
                  ( coherence-square-cocone-span-diagram s c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram s c))
                    ( d)))))
            ( pullback-property-pushout-universal-property-pushout
              ( make-span-diagram
                ( h ∘ left-map-span-diagram s)
                ( right-map-span-diagram s))
              ( vertical-comp-cocone-span-diagram s h c d)
              ( U)
              ( W))))
```

#### Extending pushouts by an equivalence of arrows on top

If we have a pushout square on the right, equivalences `S' ≃ S` and `B' ≃ B`,
and a map `g' : S' → B'` making the top square commute, then the vertical
rectangle is again a pushout. This is a special case of the vertical pushout
pasting lemma.

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
  { l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  { S' : UU l5} {B' : UU l6} (g' : S' → B')
  ( e : equiv-arrow g' (right-map-span-diagram s))
  { X : UU l4} ( c : cocone-span-diagram s X)
  where

  universal-property-pushout-cocone-right-extend-equiv-arrow-span-diagram :
    universal-property-pushout s c →
    universal-property-pushout
      ( right-extend-equiv-arrow-span-diagram s g' e)
      ( cocone-right-extend-equiv-arrow-span-diagram s g' e c)
  universal-property-pushout-cocone-right-extend-equiv-arrow-span-diagram =
    universal-property-pushout-rectangle-universal-property-pushout-top
      ( transposition-span-diagram
        ( span-diagram-equiv-arrow g' (right-map-span-diagram s) e))
      ( left-map-span-diagram s)
      ( transposition-cocone-span-diagram
        ( span-diagram-equiv-arrow g' (right-map-span-diagram s) e)
        ( cocone-equiv-arrow g' (right-map-span-diagram s) e))
      ( c)
      ( universal-property-pushout-is-equiv
        ( transposition-span-diagram
          ( span-diagram-equiv-arrow g' (right-map-span-diagram s) e))
        ( transposition-cocone-span-diagram
          ( span-diagram-equiv-arrow g' (right-map-span-diagram s) e)
          ( cocone-equiv-arrow g' (right-map-span-diagram s) e))
        ( is-equiv-map-domain-equiv-arrow g' (right-map-span-diagram s) e)
        ( is-equiv-map-codomain-equiv-arrow g' (right-map-span-diagram s) e))
```

### Extending pushouts by cocartesian morphisms of span diagrams

Given a commutative diagram

```text
         g'
    S' -----> B'
    | \        \
  f'|  \k       \j
    V   V    g ⌜ V
    A'   S -----> B
     \   |        |
     i\ ⌜| f      |
       V V        V
         A -----> X
```

in which the left and top squares are pushout squares. Then the bottom right square is a pushout square if and only if the the outer rectangle

```text
   S' ---> B'
   |       |
   |       |
   v     ⌜ v
   A' ---> X.
```

is a pushout square. In other words, pushout squares extended by [cocartesian morphisms of span diagrams](synthetic-homotopy-theory.cocartesian-morphisms-span-diagrams.md) are again pushout squares.

### Extending pushouts by equivalences of span diagrams

Given a commutative diagram where `(i , j , k)` form an
[equivalence of span diagrams](foundation.equivalences-span-diagrams.md),

```text
         g'
    S' -----> B'
    | \        \
  f'|  \k       \j
    V   V    g   V
    A'   S -----> B
     \   |        |
     i\  | f      |
       V V      ⌜ V
         A -----> X
```

the induced square is a pushout:

```text
   S' ---> B'
   |       |
   |       |
   v     ⌜ v
   A' ---> X.
```

**Proof.** We combine both cases of the pushout pasting lemmas for equivalences. The horizontal pushout pasting lemma implies that the outer rectangle

```text
          ≃        g
     S' -----> S -----> B
     |         |        |
  f' |       f |        | j
     V         V        V
     A' -----> A -----> X
          ≃        i
```

is a pushout square. The vertical pushout pasting lemma then implies that the outer square

```text
               g'
     S' --------------> B'
     |                  |
  id |                  | ≃
     V    ≃        g    V
     S' -----> S -----> B
     |         |        |
  f' |       f |        | j
     V         V        V
     A' -----> A -----> X
          ≃        i
```

is a pushout square.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (s' : span-diagram l1 l2 l3) (s : span-diagram l4 l5 l6)
  (e : equiv-span-diagram s' s)
  {X : UU l7} (c : cocone-span-diagram s X) (H : universal-property-pushout s c)
  where

  universal-property-pushout-comp-cocone-equiv-span-diagram :
    universal-property-pushout s' (comp-cocone-equiv-span-diagram s' s e c)
  universal-property-pushout-comp-cocone-equiv-span-diagram =
    universal-property-pushout-cocone-right-extend-equiv-arrow-span-diagram
      ( make-span-diagram
        ( left-map-span-diagram s')
        ( right-map-span-diagram s ∘ spanning-map-equiv-span-diagram s' s e))
      ( right-map-span-diagram s')
      ( ( id-equiv) ,
        ( equiv-codomain-equiv-span-diagram s' s e) ,
        ( right-square-equiv-span-diagram s' s e))
      ( cocone-left-extend-equiv-arrow-span-diagram s
        ( left-map-span-diagram s')
        ( equiv-left-arrow-equiv-span-diagram s' s e)
        ( c))
      ( universal-property-pushout-cocone-left-extend-equiv-arrow-span-diagram
        ( s)
        ( left-map-span-diagram s')
        ( equiv-left-arrow-equiv-span-diagram s' s e)
        ( c)
        ( H))
```

### Given an equivalence of cocones under an equivalence of span diagrams, one cocone is a pushout if and only if the other is

**Note.** The following proofs can easily be shortened if we refactor `is-pullback-bottom-is-pullback-top-cube-is-equiv`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (s : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram s X)
  (t : span-diagram l5 l6 l7) {Y : UU l8} (d : cocone-span-diagram t Y)
  (e : equiv-span-diagram s t) (e' : equiv-cocone-equiv-span-diagram s c t d e)
  where

  universal-property-pushout-equiv-cocone-equiv-span-diagram :
    universal-property-pushout t d →
    universal-property-pushout s c
  universal-property-pushout-equiv-cocone-equiv-span-diagram U =
    universal-property-pushout-pullback-property-pushout s c
      ( λ Z →
        is-pullback-bottom-is-pullback-top-cube-is-equiv
          ( precomp (left-map-cocone-span-diagram s c) Z)
          ( precomp (right-map-cocone-span-diagram s c) Z)
          ( precomp (left-map-span-diagram s) Z)
          ( precomp (right-map-span-diagram s) Z)
          ( precomp (left-map-cocone-span-diagram t d) Z)
          ( precomp (right-map-cocone-span-diagram t d) Z)
          ( precomp (left-map-span-diagram t) Z)
          ( precomp (right-map-span-diagram t) Z)
          ( precomp (map-equiv-cocone-equiv-span-diagram s c t d e e') Z)
          ( precomp (map-domain-equiv-span-diagram s t e) Z)
          ( precomp (map-codomain-equiv-span-diagram s t e) Z)
          ( precomp (spanning-map-equiv-span-diagram s t e) Z)
          ( precomp-coherence-square-maps
            ( right-map-span-diagram t)
            ( left-map-span-diagram t)
            ( right-map-cocone-span-diagram t d)
            ( left-map-cocone-span-diagram t d)
            ( coherence-square-cocone-span-diagram t d)
            ( Z))
          ( precomp-coherence-square-maps
            ( map-domain-equiv-span-diagram s t e)
            ( left-map-cocone-span-diagram s c)
            ( left-map-cocone-span-diagram t d)
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( inv-htpy
              ( left-square-equiv-cocone-equiv-span-diagram s c t d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( map-codomain-equiv-span-diagram s t e)
            ( right-map-cocone-span-diagram s c)
            ( right-map-cocone-span-diagram t d)
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( inv-htpy
              ( right-square-equiv-cocone-equiv-span-diagram s c t d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram s t e)
            ( left-map-span-diagram s)
            ( left-map-span-diagram t)
            ( map-domain-equiv-span-diagram s t e)
            ( inv-htpy (inv-htpy (left-square-equiv-span-diagram s t e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram s t e)
            ( right-map-span-diagram s)
            ( right-map-span-diagram t)
            ( map-codomain-equiv-span-diagram s t e)
            ( inv-htpy (inv-htpy (right-square-equiv-span-diagram s t e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( right-map-span-diagram s)
            ( left-map-span-diagram s)
            ( right-map-cocone-span-diagram s c)
            ( left-map-cocone-span-diagram s c)
            ( coherence-square-cocone-span-diagram s c)
            ( Z))
          ( precomp-coherence-cube-maps
            ( left-map-span-diagram t)
            ( right-map-span-diagram t)
            ( left-map-cocone-span-diagram t d)
            ( right-map-cocone-span-diagram t d)
            ( left-map-span-diagram s)
            ( right-map-span-diagram s)
            ( left-map-cocone-span-diagram s c)
            ( right-map-cocone-span-diagram s c)
            ( spanning-map-equiv-span-diagram s t e)
            ( map-domain-equiv-span-diagram s t e)
            ( map-codomain-equiv-span-diagram s t e)
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( coherence-square-cocone-span-diagram s c)
            ( inv-htpy (left-square-equiv-span-diagram s t e))
            ( inv-htpy (right-square-equiv-span-diagram s t e))
            ( left-square-equiv-cocone-equiv-span-diagram s c t d e e')
            ( right-square-equiv-cocone-equiv-span-diagram s c t d e e')
            ( coherence-square-cocone-span-diagram t d)
            ( cube-equiv-cocone-equiv-span-diagram s c t d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( is-equiv-equiv-cocone-equiv-span-diagram s c t d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-domain-equiv-span-diagram s t e)
            ( is-equiv-map-domain-equiv-span-diagram s t e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-codomain-equiv-span-diagram s t e)
            ( is-equiv-map-codomain-equiv-span-diagram s t e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( spanning-map-equiv-span-diagram s t e)
            ( is-equiv-spanning-map-equiv-span-diagram s t e)
            ( Z))
          ( pullback-property-pushout-universal-property-pushout t d U Z))

  universal-property-pushout-equiv-cocone-equiv-span-diagram' :
    universal-property-pushout s c →
    universal-property-pushout t d
  universal-property-pushout-equiv-cocone-equiv-span-diagram' U =
    universal-property-pushout-pullback-property-pushout t d
      ( λ Z →
        is-pullback-top-is-pullback-bottom-cube-is-equiv
          ( precomp (left-map-cocone-span-diagram s c) Z)
          ( precomp (right-map-cocone-span-diagram s c) Z)
          ( precomp (left-map-span-diagram s) Z)
          ( precomp (right-map-span-diagram s) Z)
          ( precomp (left-map-cocone-span-diagram t d) Z)
          ( precomp (right-map-cocone-span-diagram t d) Z)
          ( precomp (left-map-span-diagram t) Z)
          ( precomp (right-map-span-diagram t) Z)
          ( precomp (map-equiv-cocone-equiv-span-diagram s c t d e e') Z)
          ( precomp (map-domain-equiv-span-diagram s t e) Z)
          ( precomp (map-codomain-equiv-span-diagram s t e) Z)
          ( precomp (spanning-map-equiv-span-diagram s t e) Z)
          ( precomp-coherence-square-maps
            ( right-map-span-diagram t)
            ( left-map-span-diagram t)
            ( right-map-cocone-span-diagram t d)
            ( left-map-cocone-span-diagram t d)
            ( coherence-square-cocone-span-diagram t d)
            ( Z))
          ( precomp-coherence-square-maps
            ( map-domain-equiv-span-diagram s t e)
            ( left-map-cocone-span-diagram s c)
            ( left-map-cocone-span-diagram t d)
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( inv-htpy
              ( left-square-equiv-cocone-equiv-span-diagram s c t d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( map-codomain-equiv-span-diagram s t e)
            ( right-map-cocone-span-diagram s c)
            ( right-map-cocone-span-diagram t d)
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( inv-htpy
              ( right-square-equiv-cocone-equiv-span-diagram s c t d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram s t e)
            ( left-map-span-diagram s)
            ( left-map-span-diagram t)
            ( map-domain-equiv-span-diagram s t e)
            ( inv-htpy (inv-htpy (left-square-equiv-span-diagram s t e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram s t e)
            ( right-map-span-diagram s)
            ( right-map-span-diagram t)
            ( map-codomain-equiv-span-diagram s t e)
            ( inv-htpy (inv-htpy (right-square-equiv-span-diagram s t e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( right-map-span-diagram s)
            ( left-map-span-diagram s)
            ( right-map-cocone-span-diagram s c)
            ( left-map-cocone-span-diagram s c)
            ( coherence-square-cocone-span-diagram s c)
            ( Z))
          ( precomp-coherence-cube-maps
            ( left-map-span-diagram t)
            ( right-map-span-diagram t)
            ( left-map-cocone-span-diagram t d)
            ( right-map-cocone-span-diagram t d)
            ( left-map-span-diagram s)
            ( right-map-span-diagram s)
            ( left-map-cocone-span-diagram s c)
            ( right-map-cocone-span-diagram s c)
            ( spanning-map-equiv-span-diagram s t e)
            ( map-domain-equiv-span-diagram s t e)
            ( map-codomain-equiv-span-diagram s t e)
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( coherence-square-cocone-span-diagram s c)
            ( inv-htpy (left-square-equiv-span-diagram s t e))
            ( inv-htpy (right-square-equiv-span-diagram s t e))
            ( left-square-equiv-cocone-equiv-span-diagram s c t d e e')
            ( right-square-equiv-cocone-equiv-span-diagram s c t d e e')
            ( coherence-square-cocone-span-diagram t d)
            ( cube-equiv-cocone-equiv-span-diagram s c t d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-equiv-cocone-equiv-span-diagram s c t d e e')
            ( is-equiv-equiv-cocone-equiv-span-diagram s c t d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-domain-equiv-span-diagram s t e)
            ( is-equiv-map-domain-equiv-span-diagram s t e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-codomain-equiv-span-diagram s t e)
            ( is-equiv-map-codomain-equiv-span-diagram s t e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( spanning-map-equiv-span-diagram s t e)
            ( is-equiv-spanning-map-equiv-span-diagram s t e)
            ( Z))
          ( pullback-property-pushout-universal-property-pushout s c U Z))
```
