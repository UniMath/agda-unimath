# Equivalences of forks over equivalences of double arrows

```agda
module foundation.equivalences-forks-over-equivalences-double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.equivalences-double-arrows
open import foundation.forks
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.morphisms-forks-over-morphisms-double-arrows
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
```

</details>

## Idea

Consider two [double arrows](foundation.double-arrows.md) `f, g : A → B` and
`h, k : U → V`, equipped with [forks](foundation.forks.md) `c : X → A` and
`c' : Y → U`, respectively, and an
[equivalence of double arrows](foundation.equivalences-double-arrows.md)
`e : (f, g) ≃ (h, k)`. Then an
{{#concept "equivalence of forks" Disambiguation="over an equivalence of double arrows" Agda=equiv-fork-equiv-double-arrow}}
over `e` is a triple `(m, H, K)`, with `m : X ≃ Y` an
[equivalence](foundation-core.equivalences.md) of vertices of the forks, `H` a
[homotopy](foundation-core.homotopies.md) witnessing that the bottom square in
the diagram

```text
           m
     X --------> Y
     |     ≃     |
   c |           | c'
     |           |
     ∨     i     ∨
     A --------> U
    | |    ≃    | |
  f | | g     h | | k
    | |         | |
    ∨ ∨    ≃    ∨ ∨
     B --------> V
           j
```

[commutes](foundation-core.commuting-squares-of-maps.md), and `K` a coherence
datum "filling the inside" --- we have two stacks of squares

```text
           m                        m
     X --------> Y            X --------> Y
     |     ≃     |            |     ≃     |
   c |           | c'       c |           | c'
     |           |            |           |
     ∨     i     ∨            ∨     i     ∨
     A --------> U            A --------> U
     |     ≃     |            |     ≃     |
   f |           | h        g |           | k
     |           |            |           |
     ∨     ≃     ∨            ∨     ≃     ∨
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

### Equivalences of forks

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (a : double-arrow l1 l2)
  (a' : double-arrow l4 l5)
  {X : UU l3} {Y : UU l6}
  (c : fork a X) (c' : fork a' Y)
  (e : equiv-double-arrow a a')
  where

  coherence-map-fork-equiv-fork-equiv-double-arrow : (X ≃ Y) → UU (l3 ⊔ l4)
  coherence-map-fork-equiv-fork-equiv-double-arrow m =
    coherence-map-fork-hom-fork-hom-double-arrow a a' c c'
      ( hom-equiv-double-arrow a a' e)
      ( map-equiv m)

  coherence-equiv-fork-equiv-double-arrow :
    (m : X ≃ Y) → coherence-map-fork-equiv-fork-equiv-double-arrow m →
    UU (l3 ⊔ l5)
  coherence-equiv-fork-equiv-double-arrow m =
    coherence-hom-fork-hom-double-arrow a a' c c'
      ( hom-equiv-double-arrow a a' e)
      ( map-equiv m)

  equiv-fork-equiv-double-arrow : UU (l3 ⊔ l4 ⊔ l5 ⊔ l6)
  equiv-fork-equiv-double-arrow =
    Σ ( X ≃ Y)
      ( λ m →
        Σ ( coherence-map-fork-equiv-fork-equiv-double-arrow m)
          ( coherence-equiv-fork-equiv-double-arrow m))

  module _
    (e' : equiv-fork-equiv-double-arrow)
    where

    equiv-equiv-fork-equiv-double-arrow : X ≃ Y
    equiv-equiv-fork-equiv-double-arrow = pr1 e'

    map-equiv-fork-equiv-double-arrow : X → Y
    map-equiv-fork-equiv-double-arrow =
      map-equiv equiv-equiv-fork-equiv-double-arrow

    is-equiv-map-equiv-fork-equiv-double-arrow :
      is-equiv map-equiv-fork-equiv-double-arrow
    is-equiv-map-equiv-fork-equiv-double-arrow =
      is-equiv-map-equiv equiv-equiv-fork-equiv-double-arrow

    coh-map-fork-equiv-fork-equiv-double-arrow :
      coherence-map-fork-equiv-fork-equiv-double-arrow
        ( equiv-equiv-fork-equiv-double-arrow)
    coh-map-fork-equiv-fork-equiv-double-arrow = pr1 (pr2 e')

    equiv-map-fork-equiv-fork-equiv-double-arrow :
      equiv-arrow (map-fork a c) (map-fork a' c')
    pr1 equiv-map-fork-equiv-fork-equiv-double-arrow =
      equiv-equiv-fork-equiv-double-arrow
    pr1 (pr2 equiv-map-fork-equiv-fork-equiv-double-arrow) =
      domain-equiv-equiv-double-arrow a a' e
    pr2 (pr2 equiv-map-fork-equiv-fork-equiv-double-arrow) =
      coh-map-fork-equiv-fork-equiv-double-arrow

    hom-map-fork-equiv-fork-equiv-double-arrow :
      hom-arrow (map-fork a c) (map-fork a' c')
    hom-map-fork-equiv-fork-equiv-double-arrow =
      hom-equiv-arrow
        ( map-fork a c)
        ( map-fork a' c')
        ( equiv-map-fork-equiv-fork-equiv-double-arrow)

    coh-equiv-fork-equiv-double-arrow :
      coherence-equiv-fork-equiv-double-arrow
        ( equiv-equiv-fork-equiv-double-arrow)
        ( coh-map-fork-equiv-fork-equiv-double-arrow)
    coh-equiv-fork-equiv-double-arrow = pr2 (pr2 e')

    hom-equiv-fork-equiv-double-arrow :
      hom-fork-hom-double-arrow a a' c c' (hom-equiv-double-arrow a a' e)
    pr1 hom-equiv-fork-equiv-double-arrow =
      map-equiv-fork-equiv-double-arrow
    pr1 (pr2 hom-equiv-fork-equiv-double-arrow) =
      coh-map-fork-equiv-fork-equiv-double-arrow
    pr2 (pr2 hom-equiv-fork-equiv-double-arrow) =
      coh-equiv-fork-equiv-double-arrow
```

### The predicate on morphisms of forks over equivalences of double arrows of being an equivalence

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (a : double-arrow l1 l2)
  (a' : double-arrow l4 l5)
  {X : UU l3} {Y : UU l6}
  (c : fork a X) (c' : fork a' Y)
  (e : equiv-double-arrow a a')
  where

  is-equiv-hom-fork-equiv-double-arrow :
    hom-fork-hom-double-arrow a a' c c' (hom-equiv-double-arrow a a' e) →
    UU (l3 ⊔ l6)
  is-equiv-hom-fork-equiv-double-arrow h =
    is-equiv
      ( map-hom-fork-hom-double-arrow a a' c c'
        ( hom-equiv-double-arrow a a' e)
        ( h))

  is-equiv-hom-equiv-fork-equiv-double-arrow :
    (e' : equiv-fork-equiv-double-arrow a a' c c' e) →
    is-equiv-hom-fork-equiv-double-arrow
      ( hom-equiv-fork-equiv-double-arrow a a' c c' e e')
  is-equiv-hom-equiv-fork-equiv-double-arrow e' =
    is-equiv-map-equiv-fork-equiv-double-arrow a a' c c' e e'
```

## Properties

### Morphisms of forks over equivalences of arrows which are equivalences are equivalences of forks

To construct an equivalence of forks over an equivalence `e` of double arrows,
it suffices to construct a morphism of forks over the underlying morphism of
double arrows of `e`, and show that the map `X → Y` is an equivalence.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (a : double-arrow l1 l2)
  (a' : double-arrow l4 l5)
  {X : UU l3} {Y : UU l6}
  (c : fork a X) (c' : fork a' Y)
  (e : equiv-double-arrow a a')
  where

  equiv-hom-fork-equiv-double-arrow :
    (h : hom-fork-hom-double-arrow a a' c c' (hom-equiv-double-arrow a a' e)) →
    is-equiv-hom-fork-equiv-double-arrow a a' c c' e h →
    equiv-fork-equiv-double-arrow a a' c c' e
  pr1 (pr1 (equiv-hom-fork-equiv-double-arrow h is-equiv-map-fork)) =
    map-hom-fork-hom-double-arrow a a' c c' (hom-equiv-double-arrow a a' e) h
  pr2 (pr1 (equiv-hom-fork-equiv-double-arrow h is-equiv-map-fork)) =
    is-equiv-map-fork
  pr1 (pr2 (equiv-hom-fork-equiv-double-arrow h _)) =
    coh-map-fork-hom-fork-hom-double-arrow a a' c c'
      ( hom-equiv-double-arrow a a' e)
      ( h)
  pr2 (pr2 (equiv-hom-fork-equiv-double-arrow h _)) =
    coh-hom-fork-hom-double-arrow a a' c c' (hom-equiv-double-arrow a a' e) h
```
