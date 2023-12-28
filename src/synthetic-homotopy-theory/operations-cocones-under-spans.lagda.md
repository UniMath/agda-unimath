# Operations on cocones under spans

```agda
module synthetic-homotopy-theory.operations-cocones-under-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.extensions-spans
open import foundation.function-extensionality
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.spans
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
[cocones under spans](synthetic-homotopy-theory.cocones-under-span-diagrams.md)
by combining cocones with other cocones,
[morphisms of arrows](foundation.morphisms-arrows.md),
[equivalences of arrows](foundation.equivalences-arrows.md),
[morphisms of spans](foundation.morphisms-spans.md),
[equivalences of spans](foundation.equivalences-spans.md), and so on.

## Definitions

### The swapping function on cocones over spans

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

This **swapping operation** on cocones is an
[involution](foundation.involutions.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4}
  where

  swap-cocone-span : cocone-span s X → cocone-span (opposite-span s) X
  pr1 (swap-cocone-span c) = vertical-map-cocone-span s c
  pr1 (pr2 (swap-cocone-span c)) = horizontal-map-cocone-span s c
  pr2 (pr2 (swap-cocone-span c)) = inv-htpy (coherence-square-cocone-span s c)

module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) (X : UU l4)
  where

  is-involution-swap-cocone-span :
    swap-cocone-span (opposite-span s) {X} ∘ swap-cocone-span s {X} ~ id
  is-involution-swap-cocone-span c =
    eq-htpy-cocone-span s
      ( swap-cocone-span (opposite-span s) (swap-cocone-span s c))
      ( c)
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ t →
          concat
            ( right-unit)
            ( coherence-square-cocone-span s c t)
            ( inv-inv (coherence-square-cocone-span s c t))))

module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) (X : UU l4)
  where

  is-equiv-swap-cocone-span : is-equiv (swap-cocone-span s {X})
  is-equiv-swap-cocone-span =
    is-equiv-is-invertible
      ( swap-cocone-span (opposite-span s))
      ( is-involution-swap-cocone-span (opposite-span s) X)
      ( is-involution-swap-cocone-span s X)

  equiv-swap-cocone-span : cocone-span s X ≃ cocone-span (opposite-span s) X
  pr1 equiv-swap-cocone-span = swap-cocone-span s
  pr2 equiv-swap-cocone-span = is-equiv-swap-cocone-span
```

### Postcomposing cocones under spans with maps

Consider a span `A <-f- S -g-> B`. equipped with a cocone `c := (i , j , H)` as
indicated in the diagram

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
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3) {X : UU l4} {Y : UU l5}
  where

  cocone-span-map : cocone-span s X → (X → Y) → cocone-span s Y
  pr1 (cocone-span-map c h) = h ∘ horizontal-map-cocone-span s c
  pr1 (pr2 (cocone-span-map c h)) = h ∘ vertical-map-cocone-span s c
  pr2 (pr2 (cocone-span-map c h)) = h ·l coherence-square-cocone-span s c

module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4}
  where

  cocone-span-map-id :
    (c : cocone-span s X) → cocone-span-map s c id ＝ c
  cocone-span-map-id c =
    eq-pair-Σ refl
      ( eq-pair-Σ refl (eq-htpy (ap-id ∘ coherence-square-cocone-span s c)))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  where

  cocone-span-map-comp :
    (c : cocone-span s X) (h : X → Y) (k : Y → Z) →
    cocone-span-map s c (k ∘ h) ＝ cocone-span-map s (cocone-span-map s c h) k
  cocone-span-map-comp (i , j , H) h k =
    eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy (ap-comp k h ∘ H)))
```

### Horizontal composition of cocones under spans

Consider a span `s := A <-f- S -g-> B` and a moprhism `h : B → C`. Then we can
**compose** any cocone `c := (i , j , H)` with codomain `X` under the span `s`
**horizontally** with a cocone `d` under the span `X <-j- B -h-> C` as indicated
in the diagram

```text
        g       h
    S ----> B ----> C
    |       |       |
  f |       |       |
    v       v       v
    A ----> X ----> Y
```

to obtain a cocone under the span `A <-f- S -h∘g-> C`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : codomain-span s → C)
  (c : cocone-span s X)
  (d : cocone-span (make-span (vertical-map-cocone-span s c) h) Y)
  where

  horizontal-map-horizontal-comp-cocone-span : domain-span s → Y
  horizontal-map-horizontal-comp-cocone-span =
    horizontal-map-cocone-span (make-span (vertical-map-cocone-span s c) h) d ∘
    horizontal-map-cocone-span s c

  vertical-map-horizontal-comp-cocone-span : C → Y
  vertical-map-horizontal-comp-cocone-span =
    vertical-map-cocone-span (make-span (vertical-map-cocone-span s c) h) d

  coherence-square-horizontal-comp-cocone-span :
    coherence-square-maps
      ( h ∘ right-map-span s)
      ( left-map-span s)
      ( vertical-map-horizontal-comp-cocone-span)
      ( horizontal-map-horizontal-comp-cocone-span)
  coherence-square-horizontal-comp-cocone-span =
    pasting-horizontal-coherence-square-maps
      ( right-map-span s)
      ( h)
      ( left-map-span s)
      ( vertical-map-cocone-span s c)
      ( vertical-map-cocone-span (make-span (vertical-map-cocone-span s c) h) d)
      ( horizontal-map-cocone-span s c)
      ( horizontal-map-cocone-span
        ( make-span (vertical-map-cocone-span s c) h)
        ( d))
      ( coherence-square-cocone-span s c)
      ( coherence-square-cocone-span
        ( make-span (vertical-map-cocone-span s c) h)
        ( d))

  horizontal-comp-cocone-span :
    cocone-span (right-extend-span s h) Y
  pr1 horizontal-comp-cocone-span =
    horizontal-map-horizontal-comp-cocone-span
  pr1 (pr2 horizontal-comp-cocone-span) =
    vertical-map-horizontal-comp-cocone-span
  pr2 (pr2 horizontal-comp-cocone-span) =
    coherence-square-horizontal-comp-cocone-span
```

### Cocones on spans extended on the left by morphisms and equivalences of arrows

Consider a span `s := A <-f- S -g-> B`, a cocone on `s`, and a
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

Then we obtain a new cocone on the outer span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') {X : UU l6}
  where

  cocone-left-extend-hom-arrow-span :
    (h : hom-arrow f' (left-map-span s)) → cocone-span s X →
    cocone-span (left-extend-hom-arrow-span s f' h) X
  cocone-left-extend-hom-arrow-span h c =
    horizontal-comp-cocone-span
      ( span-hom-arrow f' (left-map-span s) h)
      ( right-map-span s)
      ( cocone-hom-arrow f' (left-map-span s) h)
      ( c)

  cocone-left-extend-equiv-arrow-span :
    (e : equiv-arrow f' (left-map-span s)) → cocone-span s X →
    cocone-span (left-extend-equiv-arrow-span s f' e) X
  cocone-left-extend-equiv-arrow-span e =
    cocone-left-extend-hom-arrow-span
      ( hom-equiv-arrow f' (left-map-span s) e)
```

Consider a span `s := A <-f- S -g-> B`, a cocone `(i , j , H)` on `s`, and a
moprhism of arrows `h : hom-arrow j j'` for some map `j' : B' → X'`, as
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

Then we obtain a new cocone on the outer span `A <- S -> B'`.

A variation on the above:

```text
        g       h
    S ----> B ----> C
    |       |       |
  f |     j |       | k
    v       v       v
    A ----> X ----> Y
        i
```

```text
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : codomain-span s → C)
  (j : codomain-span s → X) (i : domain-span s → X)
  where

  horizontal-comp-cocone-span' :
    cocone-span (make-span j h) Y →
    coherence-square-maps (right-map-span s) (left-map-span s) j i →
    cocone-span (right-extend-span s h) Y
  horizontal-comp-cocone-span' c coh =
    horizontal-comp-cocone-span s h (i , j , coh) c
```

### Vertical composition of cocones under spans

Consider a span `s := A <-f- S -g-> B` and a map `h : A → C`. Then we can
**compose** a cocone `c := (i , j , H)` under `s` **vertically** with a cocone
`d` under the span `C <-h- A -i-> X` as indicated in the diagram

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

to obtain a cocone under the span `C <-h∘f- S -g-> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} (h : domain-span s → C) {X : UU l5} {Y : UU l6}
  (c : cocone-span s X)
  (d : cocone-span (make-span h (horizontal-map-cocone-span s c)) Y)
  where

  horizontal-map-vertical-comp-cocone-span : C → Y
  horizontal-map-vertical-comp-cocone-span =
    horizontal-map-cocone-span (make-span h (horizontal-map-cocone-span s c)) d

  vertical-map-vertical-comp-cocone-span : codomain-span s → Y
  vertical-map-vertical-comp-cocone-span =
    vertical-map-cocone-span (make-span h (horizontal-map-cocone-span s c)) d ∘
    vertical-map-cocone-span s c

  coherence-square-vertical-comp-cocone-span :
    coherence-square-maps
      ( right-map-span s)
      ( h ∘ left-map-span s)
      ( vertical-map-vertical-comp-cocone-span)
      ( horizontal-map-vertical-comp-cocone-span)
  coherence-square-vertical-comp-cocone-span =
    pasting-vertical-coherence-square-maps
      ( right-map-span s)
      ( left-map-span s)
      ( vertical-map-cocone-span s c)
      ( horizontal-map-cocone-span s c)
      ( h)
      ( vertical-map-cocone-span
        ( make-span h (horizontal-map-cocone-span s c))
        ( d))
      ( horizontal-map-cocone-span
        ( make-span h (horizontal-map-cocone-span s c))
        ( d))
      ( coherence-square-cocone-span s c)
      ( coherence-square-cocone-span
        ( make-span h (horizontal-map-cocone-span s c))
        ( d))

  vertical-comp-cocone-span :
    cocone-span (left-extend-span s h) Y
  pr1 vertical-comp-cocone-span =
    horizontal-map-vertical-comp-cocone-span
  pr1 (pr2 vertical-comp-cocone-span) =
    vertical-map-vertical-comp-cocone-span
  pr2 (pr2 vertical-comp-cocone-span) =
    coherence-square-vertical-comp-cocone-span
```

### Composing cocones with morphisms of arrows on the right

Consider a span `s := A <-f- S -g-> B` and a map `g' : S' → B'`. Then we can
**compose** a morphism of arrows `h : hom-arrow g' g` with a cocone
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

to obtain a cocone under the span `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B') {X : UU l6}
  where

  cocone-right-extend-hom-arrow-span :
    (h : hom-arrow g' (right-map-span s)) → cocone-span s X →
    cocone-span (right-extend-hom-arrow-span s g' h) X
  cocone-right-extend-hom-arrow-span h c =
    vertical-comp-cocone-span
      ( span-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span s) h)
        ( map-codomain-hom-arrow g' (right-map-span s) h)
        ( transpose-hom-arrow g' (right-map-span s) h))
      ( left-map-span s)
      ( cocone-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span s) h)
        ( map-codomain-hom-arrow g' (right-map-span s) h)
        ( transpose-hom-arrow g' (right-map-span s) h))
      ( c)

  cocone-right-extend-equiv-arrow-span :
    (e : equiv-arrow g' (right-map-span s)) → cocone-span s X →
    cocone-span (right-extend-equiv-arrow-span s g' e) X
  cocone-right-extend-equiv-arrow-span e =
    cocone-right-extend-hom-arrow-span (hom-equiv-arrow g' (right-map-span s) e)
```

A variation on the above:

```text
        g
    S -----> B
    |        |
  f |        | j
    v   i    v
    A -----> X
    |        |
  h |        |
    v        v
    C -----> Y
```

```text
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : domain-span s → C)
  (i : domain-span s → X) (j : codomain-span s → X)
  where

  vertical-comp-cocone-span' :
    cocone-span (make-span h i) Y →
    coherence-square-maps (right-map-span s) (left-map-span s) j i →
    cocone-span (left-extend-span s h) Y
  vertical-comp-cocone-span' c coh =
    vertical-comp-cocone-span s h (i , j , coh) c
```

### Composition of cocones and morphisms of spans

Given a commutative diagram of the form

```text
          g'
     S' -----> B'
     |\         \
     | \ k       \ j
     v  v     g   v
     A'  S ------> B
      \  |         |
     i \ | f       |
        vv         v
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

Notice that the triple `(i,j,k)` is really a morphism of spans. So the resulting
cocone arises as a composition of the original cocone with this morphism of
spans.

**Note:** In the following definition we parenthesize the coherence explicitly,
because the parenthesization is relevant in future computations.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (s' : span l1 l2 l3) (s : span l4 l5 l6) (h : hom-span s' s)
  {X : UU l7} (c : cocone-span s X)
  where

  horizontal-map-comp-cocone-span-hom-span : domain-span s' → X
  horizontal-map-comp-cocone-span-hom-span =
    horizontal-map-cocone-span s c ∘ map-domain-hom-span s' s h

  vertical-map-comp-cocone-span-hom-span : codomain-span s' → X
  vertical-map-comp-cocone-span-hom-span =
    vertical-map-cocone-span s c ∘ map-codomain-hom-span s' s h

  coherence-square-comp-span-hom-span :
    coherence-square-maps
      ( right-map-span s')
      ( left-map-span s')
      ( vertical-map-comp-cocone-span-hom-span)
      ( horizontal-map-comp-cocone-span-hom-span)
  coherence-square-comp-span-hom-span =
    ( ( horizontal-map-cocone-span s c ·l left-square-hom-span s' s h) ∙h
      ( coherence-square-cocone-span s c ·r spanning-map-hom-span s' s h)) ∙h
    ( inv-htpy (vertical-map-cocone-span s c ·l right-square-hom-span s' s h))

  comp-cocone-span-hom-span : cocone-span s' X
  pr1 comp-cocone-span-hom-span = horizontal-map-comp-cocone-span-hom-span
  pr1 (pr2 comp-cocone-span-hom-span) = vertical-map-comp-cocone-span-hom-span
  pr2 (pr2 comp-cocone-span-hom-span) = coherence-square-comp-span-hom-span
```
