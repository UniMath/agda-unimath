# Morphisms of forks over morphisms of double arrows

```agda
module foundation.morphisms-forks-over-morphisms-double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.forks
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.morphisms-double-arrows
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
```

</details>

## Idea

Consider two [double arrows](foundation.double-arrows.md) `f, g : A → B` and
`h, k : U → V`, equipped with [forks](synthetic-homotopy-theory.forks.md)
`c : X → A` and `c' : Y → U`, respectively, and a
[morphism of double arrows](foundation.morphisms-double-arrows.md)
`e : (f, g) → (h, k)`.

Then a
{{#concept "morphism of forks" Disambiguation="over a morphism of double arrows" Agda=hom-fork-hom-double-arrow}}
over `e` is a triple `(m, H, K)`, with `m : X → Y` a map of vertices of the
forks, `H` a [homotopy](foundation-core.homotopies.md) witnessing that the top
square in the diagram

```text
           m
     X --------> Y
     |           |
   c |           | c'
     |           |
     ∨     i     ∨
     A --------> U
    | |         | |
  f | | g     h | | k
    | |         | |
    ∨ ∨         ∨ ∨
     B --------> V
           j
```

[commutes](foundation-core.commuting-squares-of-maps.md), and `K` a coherence
datum "filling the inside" --- we have two stacks of squares

```text
     X --------> Y            X --------> Y
     |           |            |           |
   c |           | c'       c |           | c'
     |           |            |           |
     ∨     i     ∨            ∨     i     ∨
     A --------> U            A --------> U
     |           |            |           |
   f |           | h        g |           | k
     |           |            |           |
     ∨           ∨            ∨           ∨
     B --------> V            B --------> V
           j                        j
```

which share the top map `i` and the bottom square, and the coherences of `c` and
`c'` filling the sides; that gives the homotopies

```text
                                               m                 m
     X                 X                 X --------> Y     X --------> Y
     |                 |                             |                 |
   c |               c |                             | c'              | c'
     |                 |                             |                 |
     ∨                 ∨     i                       ∨                 ∨
     A        ~        A --------> U        ~        U        ~        U
     |                             |                 |                 |
   f |                             | h               | h               | k
     |                             |                 |                 |
     ∨                             ∨                 ∨                 ∨
     B --------> V                 V                 V                 V
           j
```

and

```text
                                                                 m
     X                 X                 X                 X --------> Y
     |                 |                 |                             |
   c |               c |               c |                             | c'
     |                 |                 |                             |
     ∨                 ∨                 ∨     i                       ∨
     A        ~        A        ~        A --------> U        ~        U
     |                 |                             |                 |
   f |               g |                             | k               | k
     |                 |                             |                 |
     ∨                 ∨                             ∨                 ∨
     B --------> Y     B --------> V                 V                 V ,
           j                 j
```

which are required to be homotopic.

## Definitions

### Morphisms of forks over morphisms of double arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (a : double-arrow l1 l2) (a' : double-arrow l4 l5)
  {X : UU l3} {Y : UU l6}
  (c : fork a X) (c' : fork a' Y)
  (h : hom-double-arrow a a')
  where

  coherence-map-fork-hom-fork-hom-double-arrow : (X → Y) → UU (l3 ⊔ l4)
  coherence-map-fork-hom-fork-hom-double-arrow u =
    coherence-square-maps
      ( u)
      ( map-fork a c)
      ( map-fork a' c')
      ( domain-map-hom-double-arrow a a' h)

  coherence-hom-fork-hom-double-arrow :
    (u : X → Y) → coherence-map-fork-hom-fork-hom-double-arrow u →
    UU (l3 ⊔ l5)
  coherence-hom-fork-hom-double-arrow u H =
    ( left-square-hom-double-arrow a a' h ·r map-fork a c) ∙h
    ( ( left-map-double-arrow a' ·l H) ∙h
      ( coh-fork a' c' ·r u)) ~
    ( codomain-map-hom-double-arrow a a' h ·l coh-fork a c) ∙h
    ( ( right-square-hom-double-arrow a a' h ·r map-fork a c) ∙h
      ( right-map-double-arrow a' ·l H))

  hom-fork-hom-double-arrow : UU (l3 ⊔ l4 ⊔ l5 ⊔ l6)
  hom-fork-hom-double-arrow =
    Σ ( X → Y)
      ( λ u →
        Σ ( coherence-map-fork-hom-fork-hom-double-arrow u)
          ( coherence-hom-fork-hom-double-arrow u))
```

### Components of a morphism of forks over a morphism of double arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : fork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : fork a' Y)
  {h : hom-double-arrow a a'} (m : hom-fork-hom-double-arrow a a' c c' h)
  where

  map-hom-fork-hom-double-arrow : X → Y
  map-hom-fork-hom-double-arrow = pr1 m

  coh-map-fork-hom-fork-hom-double-arrow :
    coherence-map-fork-hom-fork-hom-double-arrow a a' c c' h
      ( map-hom-fork-hom-double-arrow)
  coh-map-fork-hom-fork-hom-double-arrow = pr1 (pr2 m)

  hom-map-fork-hom-fork-hom-double-arrow :
    hom-arrow (map-fork a c) (map-fork a' c')
  pr1 hom-map-fork-hom-fork-hom-double-arrow =
    map-hom-fork-hom-double-arrow
  pr1 (pr2 hom-map-fork-hom-fork-hom-double-arrow) =
    domain-map-hom-double-arrow a a' h
  pr2 (pr2 hom-map-fork-hom-fork-hom-double-arrow) =
    coh-map-fork-hom-fork-hom-double-arrow

  coh-hom-fork-hom-double-arrow :
    coherence-hom-fork-hom-double-arrow a a' c c' h
      ( map-hom-fork-hom-double-arrow)
      ( coh-map-fork-hom-fork-hom-double-arrow)
  coh-hom-fork-hom-double-arrow = pr2 (pr2 m)
```
