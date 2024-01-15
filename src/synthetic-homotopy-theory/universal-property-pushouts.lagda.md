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
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} → cocone-span-diagram 𝒮 X → UUω
universal-property-pushout 𝒮 c =
  {l : Level} (Y : UU l) → is-equiv (cocone-map-span-diagram 𝒮 {Y = Y} c)

module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X) (H : universal-property-pushout 𝒮 c)
  {Y : UU l5} (d : cocone-span-diagram 𝒮 Y)
  where

  map-universal-property-pushout : X → Y
  map-universal-property-pushout = map-inv-is-equiv (H Y) d

  htpy-cocone-universal-property-pushout :
    htpy-cocone-span-diagram 𝒮
      ( cocone-map-span-diagram 𝒮 c map-universal-property-pushout)
      ( d)
  htpy-cocone-universal-property-pushout =
    htpy-eq-cocone-span-diagram
      ( 𝒮)
      ( cocone-map-span-diagram 𝒮 c map-universal-property-pushout)
      ( d)
      ( is-section-map-inv-is-equiv (H Y) d)

  cocone-map-universal-property-pushout : cocone-span-diagram 𝒮 Y
  cocone-map-universal-property-pushout =
    cocone-map-span-diagram 𝒮 c map-universal-property-pushout

  left-htpy-cocone-universal-property-pushout :
    coherence-triangle-maps'
      ( left-map-cocone-span-diagram 𝒮 d)
      ( map-universal-property-pushout)
      ( left-map-cocone-span-diagram 𝒮 c)
  left-htpy-cocone-universal-property-pushout =
    left-htpy-cocone-span-diagram
      ( 𝒮)
      ( cocone-map-universal-property-pushout)
      ( d)
      ( htpy-cocone-universal-property-pushout)

  right-htpy-cocone-universal-property-pushout :
    map-universal-property-pushout ∘ right-map-cocone-span-diagram 𝒮 c ~
    right-map-cocone-span-diagram 𝒮 d
  right-htpy-cocone-universal-property-pushout =
    right-htpy-cocone-span-diagram
      ( 𝒮)
      ( cocone-map-universal-property-pushout)
      ( d)
      ( htpy-cocone-universal-property-pushout)

  coherence-htpy-cocone-universal-property-pushout :
    statement-coherence-htpy-cocone-span-diagram 𝒮
      ( cocone-map-span-diagram 𝒮 c map-universal-property-pushout)
      ( d)
      ( left-htpy-cocone-universal-property-pushout)
      ( right-htpy-cocone-universal-property-pushout)
  coherence-htpy-cocone-universal-property-pushout =
    coherence-htpy-cocone-span-diagram
      ( 𝒮)
      ( cocone-map-universal-property-pushout)
      ( d)
      ( htpy-cocone-universal-property-pushout)

  abstract
    uniqueness-map-universal-property-pushout :
      is-contr
        ( Σ ( X → Y)
            ( λ h →
              htpy-cocone-span-diagram 𝒮 (cocone-map-span-diagram 𝒮 c h) d))
    uniqueness-map-universal-property-pushout =
      is-contr-is-equiv'
        ( fiber (cocone-map-span-diagram 𝒮 c) d)
        ( tot
          ( λ h →
            htpy-eq-cocone-span-diagram 𝒮 (cocone-map-span-diagram 𝒮 c h) d))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ h →
            is-equiv-htpy-eq-cocone-span-diagram 𝒮
              ( cocone-map-span-diagram 𝒮 c h)
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
  cocone-map-span-diagram 𝒮 (i , j , H) h ~ (i' , j' , H'),
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
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  {X' : UU l5} (c' : cocone-span-diagram 𝒮 X')
  (h : X → X') (H : htpy-cocone-span-diagram 𝒮 (cocone-map-span-diagram 𝒮 c h) c')
  where

  triangle-cocone-map-span-diagram :
    {l6 : Level} (Z : UU l6) →
    coherence-triangle-maps
      ( cocone-map-span-diagram 𝒮 c')
      ( cocone-map-span-diagram 𝒮 c)
      ( precomp h Z)
  triangle-cocone-map-span-diagram Z k =
    inv
      ( ( compute-comp-cocone-map-span-diagram 𝒮 c h k) ∙
        ( ap
          ( λ t → cocone-map-span-diagram 𝒮 t k)
          ( eq-htpy-cocone-span-diagram 𝒮
            ( cocone-map-span-diagram 𝒮 c h)
            ( c')
            ( H))))

  abstract
    is-equiv-universal-property-pushout-universal-property-pushout :
      universal-property-pushout 𝒮 c →
      universal-property-pushout 𝒮 c' →
      is-equiv h
    is-equiv-universal-property-pushout-universal-property-pushout U V =
      is-equiv-is-equiv-precomp h
        ( λ Z →
          is-equiv-top-map-triangle
            ( cocone-map-span-diagram 𝒮 c')
            ( cocone-map-span-diagram 𝒮 c)
            ( precomp h Z)
            ( triangle-cocone-map-span-diagram Z)
            ( U Z)
            ( V Z))

  abstract
    universal-property-pushout-universal-property-pushout-is-equiv :
      is-equiv h →
      universal-property-pushout 𝒮 c →
      universal-property-pushout 𝒮 c'
    universal-property-pushout-universal-property-pushout-is-equiv K U Z =
      is-equiv-left-map-triangle
        ( cocone-map-span-diagram 𝒮 c')
        ( cocone-map-span-diagram 𝒮 c)
        ( precomp h Z)
        ( triangle-cocone-map-span-diagram Z)
        ( is-equiv-precomp-is-equiv h K Z)
        ( U Z)

  abstract
    universal-property-pushout-is-equiv-universal-property-pushout :
      universal-property-pushout 𝒮 c' →
      is-equiv h →
      universal-property-pushout 𝒮 c
    universal-property-pushout-is-equiv-universal-property-pushout U K Z =
      is-equiv-right-map-triangle
        ( cocone-map-span-diagram 𝒮 c')
        ( cocone-map-span-diagram 𝒮 c)
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
  cocone-map-span-diagram 𝒮 (i , j , H) (map-equiv e) ~ (i' , j' , H')
```

is contractible.

**Proof.** By the 3-for-2 property of pushouts it follows that every map
`h : X → X'` equipped with a homotopy of cocones

```text
  cocone-map-span-diagram 𝒮 (i , j , H) h ~ (i' , j' , H'),
```

is an equivalence. Furthermore, the type of such maps is contractible by the
universal property of pushouts. Hence the claim follows.

```agda
abstract
  uniquely-unique-pushout :
    { l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
    { X : UU l4} (c : cocone-span-diagram 𝒮 X)
    { Y : UU l5} (d : cocone-span-diagram 𝒮 Y) →
    universal-property-pushout 𝒮 c →
    universal-property-pushout 𝒮 d →
    is-contr
      ( Σ ( X ≃ Y)
          ( λ e →
            htpy-cocone-span-diagram 𝒮
              ( cocone-map-span-diagram 𝒮 c (map-equiv e))
              ( d)))
  uniquely-unique-pushout 𝒮 c d H K =
    is-torsorial-Eq-subtype
      ( uniqueness-map-universal-property-pushout 𝒮 c H d)
      ( is-property-is-equiv)
      ( map-universal-property-pushout 𝒮 c H d)
      ( htpy-cocone-universal-property-pushout 𝒮 c H d)
      ( is-equiv-universal-property-pushout-universal-property-pushout 𝒮 c d
        ( map-universal-property-pushout 𝒮 c H d)
        ( htpy-cocone-universal-property-pushout 𝒮 c H d)
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
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  where

  triangle-pullback-property-pushout-universal-property-pushout :
    {l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( cocone-map-span-diagram 𝒮 c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span-diagram 𝒮)
        ( _∘ right-map-span-diagram 𝒮)
        ( cone-pullback-property-pushout 𝒮 c Y))
  triangle-pullback-property-pushout-universal-property-pushout Y h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( inv
          ( is-section-eq-htpy
            ( h ·l coherence-square-cocone-span-diagram 𝒮 c))))

  pullback-property-pushout-universal-property-pushout :
    universal-property-pushout 𝒮 c → pullback-property-pushout 𝒮 c
  pullback-property-pushout-universal-property-pushout H Y =
    is-equiv-top-map-triangle
      ( cocone-map-span-diagram 𝒮 c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span-diagram 𝒮)
        ( _∘ right-map-span-diagram 𝒮)
        ( cone-pullback-property-pushout 𝒮 c Y))
      ( triangle-pullback-property-pushout-universal-property-pushout Y)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ i' →
          is-equiv-tot-is-fiberwise-equiv
            ( λ j' →
              funext
                ( i' ∘ left-map-span-diagram 𝒮)
                ( j' ∘ right-map-span-diagram 𝒮))))
      ( H Y)

  universal-property-pushout-pullback-property-pushout :
    pullback-property-pushout 𝒮 c → universal-property-pushout 𝒮 c
  universal-property-pushout-pullback-property-pushout pb-c Y =
    is-equiv-left-map-triangle
      ( cocone-map-span-diagram 𝒮 c)
      ( tot (λ i' → tot (λ j' → htpy-eq)))
      ( gap
        ( _∘ left-map-span-diagram 𝒮)
        ( _∘ right-map-span-diagram 𝒮)
        ( cone-pullback-property-pushout 𝒮 c Y))
      ( triangle-pullback-property-pushout-universal-property-pushout Y)
      ( pb-c Y)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ i' →
          is-equiv-tot-is-fiberwise-equiv
            ( λ j' →
              funext
                ( i' ∘ left-map-span-diagram 𝒮)
                ( j' ∘ right-map-span-diagram 𝒮))))
```

### If the left map of a span diagram is an equivalence, then the right map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {C : UU l4} (c : cocone-span-diagram 𝒮 C)
  where

  is-equiv-right-map-cocone-universal-property-pushout :
    is-equiv (left-map-span-diagram 𝒮) →
    universal-property-pushout 𝒮 c →
    is-equiv (right-map-cocone-span-diagram 𝒮 c)
  is-equiv-right-map-cocone-universal-property-pushout is-equiv-f H =
    is-equiv-is-equiv-precomp
      ( right-map-cocone-span-diagram 𝒮 c)
      ( λ T →
        is-equiv-is-pullback'
          ( _∘ left-map-span-diagram 𝒮)
          ( _∘ right-map-span-diagram 𝒮)
          ( cone-pullback-property-pushout 𝒮 c T)
          ( is-equiv-precomp-is-equiv (left-map-span-diagram 𝒮) is-equiv-f T)
          ( pullback-property-pushout-universal-property-pushout 𝒮 c H T))

  universal-property-pushout-is-equiv :
    is-equiv (left-map-span-diagram 𝒮) →
    is-equiv (right-map-cocone-span-diagram 𝒮 c) →
    universal-property-pushout 𝒮 c
  universal-property-pushout-is-equiv H K =
    universal-property-pushout-pullback-property-pushout 𝒮 c
      ( λ T →
        is-pullback-is-equiv'
          ( _∘ left-map-span-diagram 𝒮)
          ( _∘ right-map-span-diagram 𝒮)
          ( cone-pullback-property-pushout 𝒮 c T)
          ( is-equiv-precomp-is-equiv (left-map-span-diagram 𝒮) H T)
          ( is-equiv-precomp-is-equiv (right-map-cocone-span-diagram 𝒮 c) K T))

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
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  {C : UU l4} (c : cocone-span-diagram 𝒮 C)
  where

  is-equiv-left-map-cocone-universal-property-pushout :
    is-equiv (right-map-span-diagram 𝒮) →
    universal-property-pushout 𝒮 c →
    is-equiv (left-map-cocone-span-diagram 𝒮 c)
  is-equiv-left-map-cocone-universal-property-pushout is-equiv-g H =
    is-equiv-is-equiv-precomp
      ( left-map-cocone-span-diagram 𝒮 c)
      ( λ T →
        is-equiv-is-pullback
          ( precomp (left-map-span-diagram 𝒮) T)
          ( precomp (right-map-span-diagram 𝒮) T)
          ( cone-pullback-property-pushout 𝒮 c T)
          ( is-equiv-precomp-is-equiv (right-map-span-diagram 𝒮) is-equiv-g T)
          ( pullback-property-pushout-universal-property-pushout 𝒮 c H T))

  universal-property-pushout-is-equiv' :
    is-equiv (right-map-span-diagram 𝒮) →
    is-equiv (left-map-cocone-span-diagram 𝒮 c) →
    universal-property-pushout 𝒮 c
  universal-property-pushout-is-equiv' H K =
    universal-property-pushout-pullback-property-pushout 𝒮 c
      ( λ T →
        is-pullback-is-equiv
          ( precomp (left-map-span-diagram 𝒮) T)
          ( precomp (right-map-span-diagram 𝒮) T)
          ( cone-pullback-property-pushout 𝒮 c T)
          ( is-equiv-precomp-is-equiv (right-map-span-diagram 𝒮) H T)
          ( is-equiv-precomp-is-equiv (left-map-cocone-span-diagram 𝒮 c) K T))

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
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6}
  (h : codomain-span-diagram 𝒮 → C)
  (c : cocone-span-diagram 𝒮 X)
  (d : cocone-span-diagram (make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h) Y)
  (H : universal-property-pushout 𝒮 c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-right-square :
    universal-property-pushout
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( d) →
    universal-property-pushout
      ( right-extend-span-diagram 𝒮 h)
      ( horizontal-comp-cocone-span-diagram 𝒮 h c d)
  universal-property-pushout-rectangle-universal-property-pushout-right-square
    U =
    universal-property-pushout-pullback-property-pushout
      ( right-extend-span-diagram 𝒮 h)
      ( horizontal-comp-cocone-span-diagram 𝒮 h c d)
      ( λ W →
        tr
          ( is-pullback
            ( precomp (left-map-span-diagram 𝒮) W)
            ( precomp (h ∘ right-map-span-diagram 𝒮) W))
          ( inv
            ( eq-htpy-cone
              ( precomp (left-map-span-diagram 𝒮) W)
              ( precomp (h ∘ right-map-span-diagram 𝒮) W)
              ( cone-pullback-property-pushout
                ( right-extend-span-diagram 𝒮 h)
                ( horizontal-comp-cocone-span-diagram 𝒮 h c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp (left-map-span-diagram 𝒮) W)
                ( precomp (right-map-span-diagram 𝒮) W)
                ( precomp h W)
                ( cone-pullback-property-pushout 𝒮 c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                  ( d)
                  ( W)))
              ( ( refl-htpy) ,
                ( refl-htpy) ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( right-map-span-diagram 𝒮)
                  ( h)
                  ( left-map-span-diagram 𝒮)
                  ( right-map-cocone-span-diagram 𝒮 c)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                    ( d))
                  ( left-map-cocone-span-diagram 𝒮 c)
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                    ( d))
                  ( coherence-square-cocone-span-diagram 𝒮 c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                    ( d))))))
          ( is-pullback-rectangle-is-pullback-top
            ( precomp (left-map-span-diagram 𝒮) W)
            ( precomp (right-map-span-diagram 𝒮) W)
            ( precomp h W)
            ( cone-pullback-property-pushout 𝒮 c W)
            ( cone-pullback-property-pushout
              ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
              ( d)
              ( W))
            ( pullback-property-pushout-universal-property-pushout 𝒮 c
              ( H)
              ( W))
            ( pullback-property-pushout-universal-property-pushout
              ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
              ( d)
              ( U)
              ( W))))

  universal-property-pushout-right-square-universal-property-pushout-rectangle :
    universal-property-pushout
      ( right-extend-span-diagram 𝒮 h)
      ( horizontal-comp-cocone-span-diagram 𝒮 h c d) →
    universal-property-pushout
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( d)
  universal-property-pushout-right-square-universal-property-pushout-rectangle
    ( K)
    { l} =
    universal-property-pushout-pullback-property-pushout
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( d)
      ( λ W →
        is-pullback-top-is-pullback-rectangle
          ( precomp (left-map-span-diagram 𝒮) W)
          ( precomp (right-map-span-diagram 𝒮) W)
          ( precomp h W)
          ( cone-pullback-property-pushout 𝒮 c W)
          ( cone-pullback-property-pushout
            ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
            ( d)
            ( W))
          ( pullback-property-pushout-universal-property-pushout 𝒮 c H W)
          ( tr
            ( is-pullback
              ( precomp (left-map-span-diagram 𝒮) W)
              ( precomp (h ∘ (right-map-span-diagram 𝒮)) W))
            ( eq-htpy-cone
              ( precomp (left-map-span-diagram 𝒮) W)
              ( precomp (h ∘ right-map-span-diagram 𝒮) W)
              ( cone-pullback-property-pushout
                ( right-extend-span-diagram 𝒮 h)
                ( horizontal-comp-cocone-span-diagram 𝒮 h c d)
                ( W))
              ( pasting-vertical-cone
                ( precomp (left-map-span-diagram 𝒮) W)
                ( precomp (right-map-span-diagram 𝒮) W)
                ( precomp h W)
                ( cone-pullback-property-pushout 𝒮 c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                  ( d)
                  ( W)))
              ( ( refl-htpy) ,
                ( refl-htpy) ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-horizontal-coherence-square-maps
                  ( W)
                  ( right-map-span-diagram 𝒮)
                  ( h)
                  ( left-map-span-diagram 𝒮)
                  ( right-map-cocone-span-diagram 𝒮 c)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                    ( d))
                  ( left-map-cocone-span-diagram 𝒮 c)
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                    ( d))
                  ( coherence-square-cocone-span-diagram 𝒮 c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
                    ( d)))))
            ( pullback-property-pushout-universal-property-pushout
              ( right-extend-span-diagram 𝒮 h)
              ( horizontal-comp-cocone-span-diagram 𝒮 h c d)
              ( K)
              ( W))))
```

#### Extending pushouts by equivalences on the left

As a special case of the horizontal pushout pasting lemma we can extend a
pushout 𝒮quare by equivalences on the left.

If we have a pushout 𝒮quare on the right, equivalences S' ≃ S and A' ≃ A, and a
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
  { l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  { S' : UU l5} {A' : UU l6} (f' : S' → A')
  ( e : equiv-arrow f' (left-map-span-diagram 𝒮))
  ( c : cocone-span-diagram 𝒮 X)
  where

  universal-property-pushout-cocone-left-extend-equiv-arrow-span-diagram :
    universal-property-pushout 𝒮 c →
    universal-property-pushout
      ( left-extend-equiv-arrow-span-diagram 𝒮 f' e)
      ( cocone-left-extend-equiv-arrow-span-diagram 𝒮 f' e c)
  universal-property-pushout-cocone-left-extend-equiv-arrow-span-diagram =
    universal-property-pushout-rectangle-universal-property-pushout-right-square
      ( span-diagram-equiv-arrow f' (left-map-span-diagram 𝒮) e)
      ( right-map-span-diagram 𝒮)
      ( cocone-equiv-arrow f' (left-map-span-diagram 𝒮) e)
      ( c)
      ( universal-property-pushout-is-equiv'
        ( span-diagram-equiv-arrow f' (left-map-span-diagram 𝒮) e)
        ( cocone-equiv-arrow f' (left-map-span-diagram 𝒮) e)
        ( is-equiv-map-domain-equiv-arrow f' (left-map-span-diagram 𝒮) e)
        ( is-equiv-map-codomain-equiv-arrow f' (left-map-span-diagram 𝒮) e))
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
  { l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  { C : UU l4} {X : UU l5} {Y : UU l6} (h : domain-span-diagram 𝒮 → C)
  ( c : cocone-span-diagram 𝒮 X)
  ( d : cocone-span-diagram (make-span-diagram h (left-map-cocone-span-diagram 𝒮 c)) Y)
  ( H : universal-property-pushout 𝒮 c)
  where

  universal-property-pushout-rectangle-universal-property-pushout-top :
    ( universal-property-pushout
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( d)) →
    ( universal-property-pushout
      ( make-span-diagram
        ( h ∘ left-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒮))
      ( vertical-comp-cocone-span-diagram 𝒮 h c d))
  universal-property-pushout-rectangle-universal-property-pushout-top U =
    universal-property-pushout-pullback-property-pushout
      ( make-span-diagram
        ( h ∘ left-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒮))
      ( vertical-comp-cocone-span-diagram 𝒮 h c d)
      ( λ W →
        tr
          ( is-pullback
            ( precomp (h ∘ left-map-span-diagram 𝒮) W)
            ( precomp (right-map-span-diagram 𝒮) W))
          ( inv
            ( eq-htpy-cone
              ( precomp (h ∘ left-map-span-diagram 𝒮) W)
              ( precomp (right-map-span-diagram 𝒮) W)
              ( cone-pullback-property-pushout
                ( make-span-diagram
                  ( h ∘ left-map-span-diagram 𝒮)
                  ( right-map-span-diagram 𝒮))
                ( vertical-comp-cocone-span-diagram 𝒮 h c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp h W)
                ( precomp (left-map-span-diagram 𝒮) W)
                ( precomp (right-map-span-diagram 𝒮) W)
                ( cone-pullback-property-pushout 𝒮 c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                  ( d)
                  ( W)))
              ( ( refl-htpy) ,
                ( refl-htpy) ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( right-map-span-diagram 𝒮)
                  ( left-map-span-diagram 𝒮)
                  ( right-map-cocone-span-diagram 𝒮 c)
                  ( left-map-cocone-span-diagram 𝒮 c)
                  ( h)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                    ( d))
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                    ( d))
                  ( coherence-square-cocone-span-diagram 𝒮 c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                    ( d))))))
          ( is-pullback-rectangle-is-pullback-left-square
            ( precomp h W)
            ( precomp (left-map-span-diagram 𝒮) W)
            ( precomp (right-map-span-diagram 𝒮) W)
            ( cone-pullback-property-pushout 𝒮 c W)
            ( cone-pullback-property-pushout
              ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
              ( d)
              ( W))
            ( pullback-property-pushout-universal-property-pushout 𝒮 c H W)
            ( pullback-property-pushout-universal-property-pushout
              ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
              ( d)
              ( U)
              ( W))))

  universal-property-pushout-top-universal-property-pushout-rectangle :
    universal-property-pushout
      ( make-span-diagram
        ( h ∘ left-map-span-diagram 𝒮)
        ( right-map-span-diagram 𝒮))
      ( vertical-comp-cocone-span-diagram 𝒮 h c d) →
    universal-property-pushout
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( d)
  universal-property-pushout-top-universal-property-pushout-rectangle U =
    universal-property-pushout-pullback-property-pushout
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( d)
      ( λ W →
        is-pullback-left-square-is-pullback-rectangle
          ( precomp h W)
          ( precomp (left-map-span-diagram 𝒮) W)
          ( precomp (right-map-span-diagram 𝒮) W)
          ( cone-pullback-property-pushout 𝒮 c W)
          ( cone-pullback-property-pushout
            ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
            ( d)
            ( W))
          ( pullback-property-pushout-universal-property-pushout 𝒮 c H W)
          ( tr
            ( is-pullback
              ( precomp (h ∘ left-map-span-diagram 𝒮) W)
              ( precomp (right-map-span-diagram 𝒮) W))
            ( eq-htpy-cone
              ( precomp (h ∘ left-map-span-diagram 𝒮) W)
              ( precomp (right-map-span-diagram 𝒮) W)
              ( cone-pullback-property-pushout
                ( make-span-diagram
                  ( h ∘ left-map-span-diagram 𝒮)
                  ( right-map-span-diagram 𝒮))
                ( vertical-comp-cocone-span-diagram 𝒮 h c d)
                ( W))
              ( pasting-horizontal-cone
                ( precomp h W)
                ( precomp (left-map-span-diagram 𝒮) W)
                ( precomp (right-map-span-diagram 𝒮) W)
                ( cone-pullback-property-pushout 𝒮 c W)
                ( cone-pullback-property-pushout
                  ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                  ( d)
                  ( W)))
              ( refl-htpy ,
                refl-htpy ,
                ( right-unit-htpy) ∙h
                ( distributive-precomp-pasting-vertical-coherence-square-maps W
                  ( right-map-span-diagram 𝒮)
                  ( left-map-span-diagram 𝒮)
                  ( right-map-cocone-span-diagram 𝒮 c)
                  ( left-map-cocone-span-diagram 𝒮 c)
                  ( h)
                  ( right-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                    ( d))
                  ( left-map-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                    ( d))
                  ( coherence-square-cocone-span-diagram 𝒮 c)
                  ( coherence-square-cocone-span-diagram
                    ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
                    ( d)))))
            ( pullback-property-pushout-universal-property-pushout
              ( make-span-diagram
                ( h ∘ left-map-span-diagram 𝒮)
                ( right-map-span-diagram 𝒮))
              ( vertical-comp-cocone-span-diagram 𝒮 h c d)
              ( U)
              ( W))))
```

#### Extending pushouts by an equivalence of arrows on top

If we have a pushout 𝒮quare on the right, equivalences `S' ≃ S` and `B' ≃ B`,
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
  { l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  { S' : UU l5} {B' : UU l6} (g' : S' → B')
  ( e : equiv-arrow g' (right-map-span-diagram 𝒮))
  { X : UU l4} ( c : cocone-span-diagram 𝒮 X)
  where

  universal-property-pushout-cocone-right-extend-equiv-arrow-span-diagram :
    universal-property-pushout 𝒮 c →
    universal-property-pushout
      ( right-extend-equiv-arrow-span-diagram 𝒮 g' e)
      ( cocone-right-extend-equiv-arrow-span-diagram 𝒮 g' e c)
  universal-property-pushout-cocone-right-extend-equiv-arrow-span-diagram =
    universal-property-pushout-rectangle-universal-property-pushout-top
      ( transposition-span-diagram
        ( span-diagram-equiv-arrow g' (right-map-span-diagram 𝒮) e))
      ( left-map-span-diagram 𝒮)
      ( transposition-cocone-span-diagram
        ( span-diagram-equiv-arrow g' (right-map-span-diagram 𝒮) e)
        ( cocone-equiv-arrow g' (right-map-span-diagram 𝒮) e))
      ( c)
      ( universal-property-pushout-is-equiv
        ( transposition-span-diagram
          ( span-diagram-equiv-arrow g' (right-map-span-diagram 𝒮) e))
        ( transposition-cocone-span-diagram
          ( span-diagram-equiv-arrow g' (right-map-span-diagram 𝒮) e)
          ( cocone-equiv-arrow g' (right-map-span-diagram 𝒮) e))
        ( is-equiv-map-domain-equiv-arrow g' (right-map-span-diagram 𝒮) e)
        ( is-equiv-map-codomain-equiv-arrow g' (right-map-span-diagram 𝒮) e))
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

in which the left and top squares are pushout 𝒮quares. Then the bottom right square is a pushout 𝒮quare if and only if the the outer rectangle

```text
   S' ---> B'
   |       |
   |       |
   v     ⌜ v
   A' ---> X.
```

is a pushout 𝒮quare. In other words, pushout 𝒮quares extended by [cocartesian morphisms of span diagrams](synthetic-homotopy-theory.cocartesian-morphisms-span-diagrams.md) are again pushout 𝒮quares.

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

is a pushout 𝒮quare. The vertical pushout pasting lemma then implies that the outer square

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

is a pushout 𝒮quare.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (𝒮' : span-diagram l1 l2 l3) (𝒮 : span-diagram l4 l5 l6)
  (e : equiv-span-diagram 𝒮' 𝒮)
  {X : UU l7} (c : cocone-span-diagram 𝒮 X) (H : universal-property-pushout 𝒮 c)
  where

  universal-property-pushout-comp-cocone-equiv-span-diagram :
    universal-property-pushout 𝒮' (comp-cocone-equiv-span-diagram 𝒮' 𝒮 e c)
  universal-property-pushout-comp-cocone-equiv-span-diagram =
    universal-property-pushout-cocone-right-extend-equiv-arrow-span-diagram
      ( make-span-diagram
        ( left-map-span-diagram 𝒮')
        ( right-map-span-diagram 𝒮 ∘ spanning-map-equiv-span-diagram 𝒮' 𝒮 e))
      ( right-map-span-diagram 𝒮')
      ( ( id-equiv) ,
        ( equiv-codomain-equiv-span-diagram 𝒮' 𝒮 e) ,
        ( right-square-equiv-span-diagram 𝒮' 𝒮 e))
      ( cocone-left-extend-equiv-arrow-span-diagram 𝒮
        ( left-map-span-diagram 𝒮')
        ( equiv-left-arrow-equiv-span-diagram 𝒮' 𝒮 e)
        ( c))
      ( universal-property-pushout-cocone-left-extend-equiv-arrow-span-diagram
        ( 𝒮)
        ( left-map-span-diagram 𝒮')
        ( equiv-left-arrow-equiv-span-diagram 𝒮' 𝒮 e)
        ( c)
        ( H))
```

### Given an equivalence of cocones under an equivalence of span diagrams, one cocone is a pushout if and only if the other is

**Note.** The following proofs can easily be shortened if we refactor `is-pullback-bottom-is-pullback-top-cube-is-equiv`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (𝒮 : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram 𝒮 X)
  (𝒯 : span-diagram l5 l6 l7) {Y : UU l8} (d : cocone-span-diagram 𝒯 Y)
  (e : equiv-span-diagram 𝒮 𝒯) (e' : equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e)
  where

  universal-property-pushout-equiv-cocone-equiv-span-diagram :
    universal-property-pushout 𝒯 d →
    universal-property-pushout 𝒮 c
  universal-property-pushout-equiv-cocone-equiv-span-diagram U =
    universal-property-pushout-pullback-property-pushout 𝒮 c
      ( λ Z →
        is-pullback-bottom-is-pullback-top-cube-is-equiv
          ( precomp (left-map-cocone-span-diagram 𝒮 c) Z)
          ( precomp (right-map-cocone-span-diagram 𝒮 c) Z)
          ( precomp (left-map-span-diagram 𝒮) Z)
          ( precomp (right-map-span-diagram 𝒮) Z)
          ( precomp (left-map-cocone-span-diagram 𝒯 d) Z)
          ( precomp (right-map-cocone-span-diagram 𝒯 d) Z)
          ( precomp (left-map-span-diagram 𝒯) Z)
          ( precomp (right-map-span-diagram 𝒯) Z)
          ( precomp (map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e') Z)
          ( precomp (map-domain-equiv-span-diagram 𝒮 𝒯 e) Z)
          ( precomp (map-codomain-equiv-span-diagram 𝒮 𝒯 e) Z)
          ( precomp (spanning-map-equiv-span-diagram 𝒮 𝒯 e) Z)
          ( precomp-coherence-square-maps
            ( right-map-span-diagram 𝒯)
            ( left-map-span-diagram 𝒯)
            ( right-map-cocone-span-diagram 𝒯 d)
            ( left-map-cocone-span-diagram 𝒯 d)
            ( coherence-square-cocone-span-diagram 𝒯 d)
            ( Z))
          ( precomp-coherence-square-maps
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( left-map-cocone-span-diagram 𝒮 c)
            ( left-map-cocone-span-diagram 𝒯 d)
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( inv-htpy
              ( left-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( right-map-cocone-span-diagram 𝒮 c)
            ( right-map-cocone-span-diagram 𝒯 d)
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( inv-htpy
              ( right-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( left-map-span-diagram 𝒮)
            ( left-map-span-diagram 𝒯)
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( inv-htpy (inv-htpy (left-square-equiv-span-diagram 𝒮 𝒯 e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( right-map-span-diagram 𝒮)
            ( right-map-span-diagram 𝒯)
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( inv-htpy (inv-htpy (right-square-equiv-span-diagram 𝒮 𝒯 e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( right-map-span-diagram 𝒮)
            ( left-map-span-diagram 𝒮)
            ( right-map-cocone-span-diagram 𝒮 c)
            ( left-map-cocone-span-diagram 𝒮 c)
            ( coherence-square-cocone-span-diagram 𝒮 c)
            ( Z))
          ( precomp-coherence-cube-maps
            ( left-map-span-diagram 𝒯)
            ( right-map-span-diagram 𝒯)
            ( left-map-cocone-span-diagram 𝒯 d)
            ( right-map-cocone-span-diagram 𝒯 d)
            ( left-map-span-diagram 𝒮)
            ( right-map-span-diagram 𝒮)
            ( left-map-cocone-span-diagram 𝒮 c)
            ( right-map-cocone-span-diagram 𝒮 c)
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( coherence-square-cocone-span-diagram 𝒮 c)
            ( inv-htpy (left-square-equiv-span-diagram 𝒮 𝒯 e))
            ( inv-htpy (right-square-equiv-span-diagram 𝒮 𝒯 e))
            ( left-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( right-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( coherence-square-cocone-span-diagram 𝒯 d)
            ( cube-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( is-equiv-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( is-equiv-map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( is-equiv-map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( is-equiv-spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( Z))
          ( pullback-property-pushout-universal-property-pushout 𝒯 d U Z))

  universal-property-pushout-equiv-cocone-equiv-span-diagram' :
    universal-property-pushout 𝒮 c →
    universal-property-pushout 𝒯 d
  universal-property-pushout-equiv-cocone-equiv-span-diagram' U =
    universal-property-pushout-pullback-property-pushout 𝒯 d
      ( λ Z →
        is-pullback-top-is-pullback-bottom-cube-is-equiv
          ( precomp (left-map-cocone-span-diagram 𝒮 c) Z)
          ( precomp (right-map-cocone-span-diagram 𝒮 c) Z)
          ( precomp (left-map-span-diagram 𝒮) Z)
          ( precomp (right-map-span-diagram 𝒮) Z)
          ( precomp (left-map-cocone-span-diagram 𝒯 d) Z)
          ( precomp (right-map-cocone-span-diagram 𝒯 d) Z)
          ( precomp (left-map-span-diagram 𝒯) Z)
          ( precomp (right-map-span-diagram 𝒯) Z)
          ( precomp (map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e') Z)
          ( precomp (map-domain-equiv-span-diagram 𝒮 𝒯 e) Z)
          ( precomp (map-codomain-equiv-span-diagram 𝒮 𝒯 e) Z)
          ( precomp (spanning-map-equiv-span-diagram 𝒮 𝒯 e) Z)
          ( precomp-coherence-square-maps
            ( right-map-span-diagram 𝒯)
            ( left-map-span-diagram 𝒯)
            ( right-map-cocone-span-diagram 𝒯 d)
            ( left-map-cocone-span-diagram 𝒯 d)
            ( coherence-square-cocone-span-diagram 𝒯 d)
            ( Z))
          ( precomp-coherence-square-maps
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( left-map-cocone-span-diagram 𝒮 c)
            ( left-map-cocone-span-diagram 𝒯 d)
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( inv-htpy
              ( left-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( right-map-cocone-span-diagram 𝒮 c)
            ( right-map-cocone-span-diagram 𝒯 d)
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( inv-htpy
              ( right-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e'))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( left-map-span-diagram 𝒮)
            ( left-map-span-diagram 𝒯)
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( inv-htpy (inv-htpy (left-square-equiv-span-diagram 𝒮 𝒯 e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( right-map-span-diagram 𝒮)
            ( right-map-span-diagram 𝒯)
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( inv-htpy (inv-htpy (right-square-equiv-span-diagram 𝒮 𝒯 e)))
            ( Z))
          ( precomp-coherence-square-maps
            ( right-map-span-diagram 𝒮)
            ( left-map-span-diagram 𝒮)
            ( right-map-cocone-span-diagram 𝒮 c)
            ( left-map-cocone-span-diagram 𝒮 c)
            ( coherence-square-cocone-span-diagram 𝒮 c)
            ( Z))
          ( precomp-coherence-cube-maps
            ( left-map-span-diagram 𝒯)
            ( right-map-span-diagram 𝒯)
            ( left-map-cocone-span-diagram 𝒯 d)
            ( right-map-cocone-span-diagram 𝒯 d)
            ( left-map-span-diagram 𝒮)
            ( right-map-span-diagram 𝒮)
            ( left-map-cocone-span-diagram 𝒮 c)
            ( right-map-cocone-span-diagram 𝒮 c)
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( coherence-square-cocone-span-diagram 𝒮 c)
            ( inv-htpy (left-square-equiv-span-diagram 𝒮 𝒯 e))
            ( inv-htpy (right-square-equiv-span-diagram 𝒮 𝒯 e))
            ( left-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( right-square-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( coherence-square-cocone-span-diagram 𝒯 d)
            ( cube-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( is-equiv-equiv-cocone-equiv-span-diagram 𝒮 c 𝒯 d e e')
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( is-equiv-map-domain-equiv-span-diagram 𝒮 𝒯 e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( is-equiv-map-codomain-equiv-span-diagram 𝒮 𝒯 e)
            ( Z))
          ( is-equiv-precomp-is-equiv
            ( spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( is-equiv-spanning-map-equiv-span-diagram 𝒮 𝒯 e)
            ( Z))
          ( pullback-property-pushout-universal-property-pushout 𝒮 c U Z))
```
