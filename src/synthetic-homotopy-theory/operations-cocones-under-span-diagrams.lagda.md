# Operations on cocones under span diagrams

```agda
module synthetic-homotopy-theory.operations-cocones-under-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.equivalences-span-diagrams
open import foundation.extensions-span-diagrams
open import foundation.function-extensionality
open import foundation.morphisms-arrows
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.transposition-span-diagrams
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

There are several ways of producing
[cocones under span diagrams](synthetic-homotopy-theory.cocones-under-span-diagrams.md)
by combining cocones with other cocones,
[morphisms of arrows](foundation.morphisms-arrows.md),
[equivalences of arrows](foundation.equivalences-arrows.md),
[morphisms of span diagrams](foundation.morphisms-span-diagrams.md),
[equivalences of span diagrams](foundation.equivalences-span-diagrams.md), and
so on.

## Definitions

### Transposing cocones under span diagrams

Any cocone

```text
        g
    S -----> B
    |        |
  f |        | j
    V        V
    A -----> X
        i
```

induces a cocone

```text
        f
    S -----> A
    |        |
  g |        | i
    V        V
    B -----> X.
        j
```

This {{#concept "transposition" Disambiguation="cocones under span diagrams"}}
on cocones is an [involution](foundation.involutions.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) {X : UU l4}
  where

  transposition-cocone-span-diagram :
    cocone-span-diagram s X →
    cocone-span-diagram (transposition-span-diagram s) X
  pr1 (transposition-cocone-span-diagram c) =
    vertical-map-cocone-span-diagram s c
  pr1 (pr2 (transposition-cocone-span-diagram c)) =
    horizontal-map-cocone-span-diagram s c
  pr2 (pr2 (transposition-cocone-span-diagram c)) =
    inv-htpy (coherence-square-cocone-span-diagram s c)

module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) (X : UU l4)
  where

  is-involution-transposition-cocone-span-diagram :
    transposition-cocone-span-diagram (transposition-span-diagram s) {X} ∘
    transposition-cocone-span-diagram s {X} ~
    id
  is-involution-transposition-cocone-span-diagram c =
    eq-htpy-cocone-span-diagram s
      ( transposition-cocone-span-diagram
        ( transposition-span-diagram s)
        ( transposition-cocone-span-diagram s c))
      ( c)
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ t →
          concat
            ( right-unit)
            ( coherence-square-cocone-span-diagram s c t)
            ( inv-inv (coherence-square-cocone-span-diagram s c t))))

module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) (X : UU l4)
  where

  is-equiv-transposition-cocone-span-diagram :
    is-equiv (transposition-cocone-span-diagram s {X})
  is-equiv-transposition-cocone-span-diagram =
    is-equiv-is-invertible
      ( transposition-cocone-span-diagram (transposition-span-diagram s))
      ( is-involution-transposition-cocone-span-diagram
        ( transposition-span-diagram s)
        ( X))
      ( is-involution-transposition-cocone-span-diagram s X)

  equiv-transposition-cocone-span-diagram :
    cocone-span-diagram s X ≃
    cocone-span-diagram (transposition-span-diagram s) X
  pr1 equiv-transposition-cocone-span-diagram =
    transposition-cocone-span-diagram s
  pr2 equiv-transposition-cocone-span-diagram =
    is-equiv-transposition-cocone-span-diagram
```

### Postcomposing cocones under span diagrams with maps

Consider a span diagram `A <-f- S -g-> B`. equipped with a cocone
`c := (i , j , H)` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |   H    | j
    V        V
    A -----> X.
        i
```

Then any map `h : X → Y` induces a cocone

```text
         g
    S -------> B
    |          |
  f |  h · H   | h ∘ j
    V          V
    A -------> Y.
       h ∘ i
```

This way of extending cocones by maps is used to express the
[universal property of pushouts](synthetic-homotopy-theory.universal-property-pushouts.md).

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3) {X : UU l4} {Y : UU l5}
  where

  cocone-map-span-diagram :
    cocone-span-diagram s X → (X → Y) → cocone-span-diagram s Y
  pr1 (cocone-map-span-diagram c h) =
    h ∘ horizontal-map-cocone-span-diagram s c
  pr1 (pr2 (cocone-map-span-diagram c h)) =
    h ∘ vertical-map-cocone-span-diagram s c
  pr2 (pr2 (cocone-map-span-diagram c h)) =
    h ·l coherence-square-cocone-span-diagram s c

module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) {X : UU l4}
  where

  compute-id-cocone-map-span-diagram :
    (c : cocone-span-diagram s X) → cocone-map-span-diagram s c id ＝ c
  compute-id-cocone-map-span-diagram c =
    eq-pair-Σ refl
      ( eq-pair-Σ refl
        ( eq-htpy (ap-id ∘ coherence-square-cocone-span-diagram s c)))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  where

  compute-comp-cocone-map-span-diagram :
    (c : cocone-span-diagram s X) (h : X → Y) (k : Y → Z) →
    cocone-map-span-diagram s c (k ∘ h) ＝
    cocone-map-span-diagram s (cocone-map-span-diagram s c h) k
  compute-comp-cocone-map-span-diagram (i , j , H) h k =
    eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy (ap-comp k h ∘ H)))
```

### Horizontal composition of cocones under span diagrams

Consider a span diagram `s := A <-f- S -g-> B` and a moprhism `h : B → C`. Then
we can **compose** any cocone `c := (i , j , H)` with codomain `X` under the
span diagram `s` **horizontally** with a cocone `d` under the span diagram
`X <-j- B -h-> C` as indicated in the diagram

```text
        g       h
    S ----> B ----> C
    |       |       |
  f |       |       |
    v       v       v
    A ----> X ----> Y
```

to obtain a cocone under the span diagram `A <-f- S -h∘g-> C`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : codomain-span-diagram s → C)
  (c : cocone-span-diagram s X)
  (d :
    cocone-span-diagram
      ( make-span-diagram (vertical-map-cocone-span-diagram s c) h)
      ( Y))
  where

  horizontal-map-horizontal-comp-cocone-span-diagram :
    domain-span-diagram s → Y
  horizontal-map-horizontal-comp-cocone-span-diagram =
    horizontal-map-cocone-span-diagram
      ( make-span-diagram (vertical-map-cocone-span-diagram s c) h)
      ( d) ∘
    horizontal-map-cocone-span-diagram s c

  vertical-map-horizontal-comp-cocone-span-diagram : C → Y
  vertical-map-horizontal-comp-cocone-span-diagram =
    vertical-map-cocone-span-diagram
      ( make-span-diagram (vertical-map-cocone-span-diagram s c) h)
      ( d)

  coherence-square-horizontal-comp-cocone-span-diagram :
    coherence-square-maps
      ( h ∘ right-map-span-diagram s)
      ( left-map-span-diagram s)
      ( vertical-map-horizontal-comp-cocone-span-diagram)
      ( horizontal-map-horizontal-comp-cocone-span-diagram)
  coherence-square-horizontal-comp-cocone-span-diagram =
    pasting-horizontal-coherence-square-maps
      ( right-map-span-diagram s)
      ( h)
      ( left-map-span-diagram s)
      ( vertical-map-cocone-span-diagram s c)
      ( vertical-map-cocone-span-diagram
        ( make-span-diagram (vertical-map-cocone-span-diagram s c) h)
        ( d))
      ( horizontal-map-cocone-span-diagram s c)
      ( horizontal-map-cocone-span-diagram
        ( make-span-diagram (vertical-map-cocone-span-diagram s c) h)
        ( d))
      ( coherence-square-cocone-span-diagram s c)
      ( coherence-square-cocone-span-diagram
        ( make-span-diagram (vertical-map-cocone-span-diagram s c) h)
        ( d))

  horizontal-comp-cocone-span-diagram :
    cocone-span-diagram (right-extend-span-diagram s h) Y
  pr1 horizontal-comp-cocone-span-diagram =
    horizontal-map-horizontal-comp-cocone-span-diagram
  pr1 (pr2 horizontal-comp-cocone-span-diagram) =
    vertical-map-horizontal-comp-cocone-span-diagram
  pr2 (pr2 horizontal-comp-cocone-span-diagram) =
    coherence-square-horizontal-comp-cocone-span-diagram
```

### Cocones under span diagrams extended on the left by morphisms and equivalences of arrows

Consider a span diagram `s := A <-f- S -g-> B`, a cocone on `s`, and a
[moprhism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f` for
some map `f : S' → A'`, as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |         |        |
  f' |    h    | f      | j
     v         v        v
     A' -----> A -----> X
          h₁       i
```

Then we obtain a new cocone on the outer span diagram `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') {X : UU l6}
  where

  cocone-left-extend-hom-arrow-span-diagram :
    (h : hom-arrow f' (left-map-span-diagram s)) → cocone-span-diagram s X →
    cocone-span-diagram (left-extend-hom-arrow-span-diagram s f' h) X
  cocone-left-extend-hom-arrow-span-diagram h c =
    horizontal-comp-cocone-span-diagram
      ( span-diagram-hom-arrow f' (left-map-span-diagram s) h)
      ( right-map-span-diagram s)
      ( cocone-hom-arrow f' (left-map-span-diagram s) h)
      ( c)

  cocone-left-extend-equiv-arrow-span-diagram :
    (e : equiv-arrow f' (left-map-span-diagram s)) → cocone-span-diagram s X →
    cocone-span-diagram (left-extend-equiv-arrow-span-diagram s f' e) X
  cocone-left-extend-equiv-arrow-span-diagram e =
    cocone-left-extend-hom-arrow-span-diagram
      ( hom-equiv-arrow f' (left-map-span-diagram s) e)
```

Consider a span diagram `s := A <-f- S -g-> B`, a cocone `(i , j , H)` on `s`,
and a moprhism of arrows `h : hom-arrow j j'` for some map `j' : B' → X'`, as
indicated in the diagram

```text
        g        h₀
    S -----> B -----> B'
    |        |        |
  f |      j |   h    | j'
    v        v        ∨
    A -----> X -----> X'
        i        h₁
```

Then we obtain a new cocone on the outer span diagram `A <- S -> B'`.

### Vertical composition of cocones under span diagrams

Consider a span diagram `s := A <-f- S -g-> B` and a map `h : A → C`. Then we
can **compose** a cocone `c := (i , j , H)` under `s` **vertically** with a
cocone `d` under the span diagram `C <-h- A -i-> X` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |        |
    v        v
    A -----> X
    |        |
  h |        |
    v        v
    C -----> Y
```

to obtain a cocone under the span diagram `C <-h∘f- S -g-> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {C : UU l4} (h : domain-span-diagram s → C) {X : UU l5} {Y : UU l6}
  (c : cocone-span-diagram s X)
  (d :
    cocone-span-diagram
      ( make-span-diagram h (horizontal-map-cocone-span-diagram s c))
      ( Y))
  where

  horizontal-map-vertical-comp-cocone-span-diagram : C → Y
  horizontal-map-vertical-comp-cocone-span-diagram =
    horizontal-map-cocone-span-diagram
      ( make-span-diagram h (horizontal-map-cocone-span-diagram s c))
      ( d)

  vertical-map-vertical-comp-cocone-span-diagram : codomain-span-diagram s → Y
  vertical-map-vertical-comp-cocone-span-diagram =
    vertical-map-cocone-span-diagram
      ( make-span-diagram h (horizontal-map-cocone-span-diagram s c))
      ( d) ∘
    vertical-map-cocone-span-diagram s c

  coherence-square-vertical-comp-cocone-span-diagram :
    coherence-square-maps
      ( right-map-span-diagram s)
      ( h ∘ left-map-span-diagram s)
      ( vertical-map-vertical-comp-cocone-span-diagram)
      ( horizontal-map-vertical-comp-cocone-span-diagram)
  coherence-square-vertical-comp-cocone-span-diagram =
    pasting-vertical-coherence-square-maps
      ( right-map-span-diagram s)
      ( left-map-span-diagram s)
      ( vertical-map-cocone-span-diagram s c)
      ( horizontal-map-cocone-span-diagram s c)
      ( h)
      ( vertical-map-cocone-span-diagram
        ( make-span-diagram h (horizontal-map-cocone-span-diagram s c))
        ( d))
      ( horizontal-map-cocone-span-diagram
        ( make-span-diagram h (horizontal-map-cocone-span-diagram s c))
        ( d))
      ( coherence-square-cocone-span-diagram s c)
      ( coherence-square-cocone-span-diagram
        ( make-span-diagram h (horizontal-map-cocone-span-diagram s c))
        ( d))

  vertical-comp-cocone-span-diagram :
    cocone-span-diagram (left-extend-span-diagram s h) Y
  pr1 vertical-comp-cocone-span-diagram =
    horizontal-map-vertical-comp-cocone-span-diagram
  pr1 (pr2 vertical-comp-cocone-span-diagram) =
    vertical-map-vertical-comp-cocone-span-diagram
  pr2 (pr2 vertical-comp-cocone-span-diagram) =
    coherence-square-vertical-comp-cocone-span-diagram
```

### Composing cocones with morphisms of arrows on the right

Consider a span diagram `s := A <-f- S -g-> B` and a map `g' : S' → B'`. Then we
can **compose** a morphism of arrows `h : hom-arrow g' g` with a cocone
`c := (i , j , H)` under `s`, as indicated in the diagram

```text
         g'
     S' ----> B'
     |        |
  h₀ |        | h₁
     v   g    v
     S -----> B
     |        |
   f |        |
     v        v
     A -----> X
```

to obtain a cocone under the span diagram `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B') {X : UU l6}
  where

  cocone-right-extend-hom-arrow-span-diagram :
    (h : hom-arrow g' (right-map-span-diagram s)) → cocone-span-diagram s X →
    cocone-span-diagram (right-extend-hom-arrow-span-diagram s g' h) X
  cocone-right-extend-hom-arrow-span-diagram h c =
    vertical-comp-cocone-span-diagram
      ( span-diagram-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span-diagram s) h)
        ( map-codomain-hom-arrow g' (right-map-span-diagram s) h)
        ( transpose-hom-arrow g' (right-map-span-diagram s) h))
      ( left-map-span-diagram s)
      ( cocone-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span-diagram s) h)
        ( map-codomain-hom-arrow g' (right-map-span-diagram s) h)
        ( transpose-hom-arrow g' (right-map-span-diagram s) h))
      ( c)

  cocone-right-extend-equiv-arrow-span-diagram :
    (e : equiv-arrow g' (right-map-span-diagram s)) → cocone-span-diagram s X →
    cocone-span-diagram (right-extend-equiv-arrow-span-diagram s g' e) X
  cocone-right-extend-equiv-arrow-span-diagram e =
    cocone-right-extend-hom-arrow-span-diagram
      ( hom-equiv-arrow g' (right-map-span-diagram s) e)
```

### Composition of cocones and morphisms of span diagrams

Given a commutative diagram of the form

```text
          g'
     S' ------> B'
     | \         \
     |  \ k       \ j
     v   v     g   v
     A'   S ------> B
      \   |         |
     i \  | f       |
        v v         v
          A ------> X
```

we can compose both vertically and horizontally to get the following cocone:

```text
   S' ---> B'
   |       |
   |       |
   v       v
   A' ---> X
```

Notice that the triple `(i,j,k)` is really a morphism of span diagrams. So the
resulting cocone arises as a composition of the original cocone with this
morphism of span diagrams.

**Note:** In the following definition we parenthesize the coherence explicitly,
because the parenthesization is relevant in future computations.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (s' : span-diagram l1 l2 l3) (s : span-diagram l4 l5 l6)
  (h : hom-span-diagram s' s)
  {X : UU l7} (c : cocone-span-diagram s X)
  where

  horizontal-map-comp-cocone-hom-span-diagram :
    domain-span-diagram s' → X
  horizontal-map-comp-cocone-hom-span-diagram =
    horizontal-map-cocone-span-diagram s c ∘ map-domain-hom-span-diagram s' s h

  vertical-map-comp-cocone-hom-span-diagram :
    codomain-span-diagram s' → X
  vertical-map-comp-cocone-hom-span-diagram =
    vertical-map-cocone-span-diagram s c ∘ map-codomain-hom-span-diagram s' s h

  coherence-square-comp-hom-span-diagram :
    coherence-square-maps
      ( right-map-span-diagram s')
      ( left-map-span-diagram s')
      ( vertical-map-comp-cocone-hom-span-diagram)
      ( horizontal-map-comp-cocone-hom-span-diagram)
  coherence-square-comp-hom-span-diagram =
    ( ( horizontal-map-cocone-span-diagram s c ·l
        left-square-hom-span-diagram s' s h) ∙h
      ( coherence-square-cocone-span-diagram s c ·r
        spanning-map-hom-span-diagram s' s h)) ∙h
    ( inv-htpy
      ( vertical-map-cocone-span-diagram s c ·l
        right-square-hom-span-diagram s' s h))

  comp-cocone-hom-span-diagram : cocone-span-diagram s' X
  pr1 comp-cocone-hom-span-diagram =
    horizontal-map-comp-cocone-hom-span-diagram
  pr1 (pr2 comp-cocone-hom-span-diagram) =
    vertical-map-comp-cocone-hom-span-diagram
  pr2 (pr2 comp-cocone-hom-span-diagram) =
    coherence-square-comp-hom-span-diagram

module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (s' : span-diagram l1 l2 l3) (s : span-diagram l4 l5 l6)
  (e : equiv-span-diagram s' s)
  {X : UU l7} (c : cocone-span-diagram s X)
  where

  comp-cocone-equiv-span-diagram : cocone-span-diagram s' X
  comp-cocone-equiv-span-diagram =
    comp-cocone-hom-span-diagram s' s (hom-equiv-span-diagram s' s e) c
```
