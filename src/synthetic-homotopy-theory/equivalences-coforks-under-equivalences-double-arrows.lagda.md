# Equivalences of coforks under equivalences of double arrows

```agda
module synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.equivalences-double-arrows
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrows
```

</details>

## Idea

Consider two [double arrows](foundation.double-arrows.md) `f, g : A → B` and
`h, k : U → V`, equipped with [coforks](synthetic-homotopy-theory.coforks.md)
`c : B → X` and `c' : V → Y`, respectively, and an
[equivalence of double arrows](foundation.equivalences-double-arrows.md)
`e : (f, g) ≃ (h, k)`.

Then an
{{#concept "equivalence of coforks" Disambiguation="under an equivalence of double arrows" Agda=equiv-cofork-equiv-double-arrow}}
under `e` is a triple `(m, H, K)`, with `m : X ≃ Y` an
[equivalence](foundation-core.equivalences.md) of vertices of the coforks, `H` a
[homotopy](foundation-core.homotopies.md) witnessing that the bottom square in
the diagram

```text
           i
     A --------> U
    | |    ≃    | |
  f | | g     h | | k
    | |         | |
    ∨ ∨    ≃    ∨ ∨
     B --------> V
     |     j     |
   c |           | c'
     |           |
     ∨     ≃     ∨
     X --------> Y
           m
```

[commutes](foundation-core.commuting-squares-of-maps.md), and `K` a coherence
datum "filling the inside" --- we have two stacks of squares

```text
           i                        i
     A --------> U            A --------> U
     |     ≃     |            |     ≃     |
   f |           | h        g |           | k
     |           |            |           |
     ∨     ≃     ∨            ∨     ≃     ∨
     B --------> V            B --------> V
     |     j     |            |     j     |
   c |           | c'       c |           | c'
     |           |            |           |
     ∨     ≃     ∨            ∨     ≃     ∨
     X --------> Y            X --------> Y
           m                        m
```

which share the top map `i` and the bottom square, and the coherences of `c` and
`c'` filling the sides; that gives the homotopies

```text
                                               i                 i
     A                 A                 A --------> U     A --------> U
     |                 |                             |                 |
   f |               f |                             | h               | k
     |                 |                             |                 |
     ∨                 ∨     j                       ∨                 ∨
     B        ~        B --------> V        ~        V        ~        V
     |                             |                 |                 |
   c |                             | c'              | c'              | c'
     |                             |                 |                 |
     ∨                             ∨                 ∨                 ∨
     X --------> Y                 Y                 Y                 Y
           m
```

and

```text
                                                                 i
     A                 A                 A                 A --------> U
     |                 |                 |                             |
   f |               g |               g |                             | k
     |                 |                 |                             |
     ∨                 ∨                 ∨     j                       ∨
     B        ~        B        ~        B --------> V        ~        V
     |                 |                             |                 |
   c |               c |                             | c'              | c'
     |                 |                             |                 |
     ∨                 ∨                             ∨                 ∨
     X --------> Y     X --------> Y                 Y                 Y ,
           m                 m
```

which are required to be homotopic.

## Definitions

### Equivalences of coforks

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  (e : equiv-double-arrow a a')
  where

  coherence-map-cofork-equiv-cofork-equiv-double-arrow : (X ≃ Y) → UU (l2 ⊔ l6)
  coherence-map-cofork-equiv-cofork-equiv-double-arrow m =
    coherence-map-cofork-hom-cofork-hom-double-arrow c c'
      ( hom-equiv-double-arrow a a' e)
      ( map-equiv m)

  coherence-equiv-cofork-equiv-double-arrow :
    (m : X ≃ Y) → coherence-map-cofork-equiv-cofork-equiv-double-arrow m →
    UU (l1 ⊔ l6)
  coherence-equiv-cofork-equiv-double-arrow m =
    coherence-hom-cofork-hom-double-arrow c c'
      ( hom-equiv-double-arrow a a' e)
      ( map-equiv m)

  equiv-cofork-equiv-double-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l6)
  equiv-cofork-equiv-double-arrow =
    Σ ( X ≃ Y)
      ( λ m →
        Σ ( coherence-map-cofork-equiv-cofork-equiv-double-arrow m)
          ( coherence-equiv-cofork-equiv-double-arrow m))

  module _
    (e' : equiv-cofork-equiv-double-arrow)
    where

    equiv-equiv-cofork-equiv-double-arrow : X ≃ Y
    equiv-equiv-cofork-equiv-double-arrow = pr1 e'

    map-equiv-cofork-equiv-double-arrow : X → Y
    map-equiv-cofork-equiv-double-arrow =
      map-equiv equiv-equiv-cofork-equiv-double-arrow

    is-equiv-map-equiv-cofork-equiv-double-arrow :
      is-equiv map-equiv-cofork-equiv-double-arrow
    is-equiv-map-equiv-cofork-equiv-double-arrow =
      is-equiv-map-equiv equiv-equiv-cofork-equiv-double-arrow

    coh-map-cofork-equiv-cofork-equiv-double-arrow :
      coherence-map-cofork-equiv-cofork-equiv-double-arrow
        ( equiv-equiv-cofork-equiv-double-arrow)
    coh-map-cofork-equiv-cofork-equiv-double-arrow = pr1 (pr2 e')

    equiv-map-cofork-equiv-cofork-equiv-double-arrow :
      equiv-arrow (map-cofork a c) (map-cofork a' c')
    pr1 equiv-map-cofork-equiv-cofork-equiv-double-arrow =
      codomain-equiv-equiv-double-arrow a a' e
    pr1 (pr2 equiv-map-cofork-equiv-cofork-equiv-double-arrow) =
      equiv-equiv-cofork-equiv-double-arrow
    pr2 (pr2 equiv-map-cofork-equiv-cofork-equiv-double-arrow) =
      coh-map-cofork-equiv-cofork-equiv-double-arrow

    hom-map-cofork-equiv-cofork-equiv-double-arrow :
      hom-arrow (map-cofork a c) (map-cofork a' c')
    hom-map-cofork-equiv-cofork-equiv-double-arrow =
      hom-equiv-arrow
        ( map-cofork a c)
        ( map-cofork a' c')
        ( equiv-map-cofork-equiv-cofork-equiv-double-arrow)

    coh-equiv-cofork-equiv-double-arrow :
      coherence-equiv-cofork-equiv-double-arrow
        ( equiv-equiv-cofork-equiv-double-arrow)
        ( coh-map-cofork-equiv-cofork-equiv-double-arrow)
    coh-equiv-cofork-equiv-double-arrow = pr2 (pr2 e')

    hom-equiv-cofork-equiv-double-arrow :
      hom-cofork-hom-double-arrow c c' (hom-equiv-double-arrow a a' e)
    pr1 hom-equiv-cofork-equiv-double-arrow =
      map-equiv-cofork-equiv-double-arrow
    pr1 (pr2 hom-equiv-cofork-equiv-double-arrow) =
      coh-map-cofork-equiv-cofork-equiv-double-arrow
    pr2 (pr2 hom-equiv-cofork-equiv-double-arrow) =
      coh-equiv-cofork-equiv-double-arrow
```

### The predicate on morphisms of coforks under equivalences of double arrows of being an equivalence

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  (e : equiv-double-arrow a a')
  where

  is-equiv-hom-cofork-equiv-double-arrow :
    hom-cofork-hom-double-arrow c c' (hom-equiv-double-arrow a a' e) →
    UU (l3 ⊔ l6)
  is-equiv-hom-cofork-equiv-double-arrow h =
    is-equiv
      ( map-hom-cofork-hom-double-arrow c c' h)

  is-equiv-hom-equiv-cofork-equiv-double-arrow :
    (e' : equiv-cofork-equiv-double-arrow c c' e) →
    is-equiv-hom-cofork-equiv-double-arrow
      ( hom-equiv-cofork-equiv-double-arrow c c' e e')
  is-equiv-hom-equiv-cofork-equiv-double-arrow e' =
    is-equiv-map-equiv-cofork-equiv-double-arrow c c' e e'
```

## Properties

### Morphisms of coforks under equivalences of arrows which are equivalences are equivalences of coforks

To construct an equivalence of coforks under an equivalence `e` of double
arrows, it suffices to construct a morphism of coforks under the underlying
morphism of double arrows of `e`, and show that the map `X → Y` is an
equivalence.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  (e : equiv-double-arrow a a')
  where

  equiv-hom-cofork-equiv-double-arrow :
    (h : hom-cofork-hom-double-arrow c c' (hom-equiv-double-arrow a a' e)) →
    is-equiv-hom-cofork-equiv-double-arrow c c' e h →
    equiv-cofork-equiv-double-arrow c c' e
  pr1 (equiv-hom-cofork-equiv-double-arrow h is-equiv-map-cofork) =
    (map-hom-cofork-hom-double-arrow c c' h , is-equiv-map-cofork)
  pr1 (pr2 (equiv-hom-cofork-equiv-double-arrow h _)) =
    coh-map-cofork-hom-cofork-hom-double-arrow c c' h
  pr2 (pr2 (equiv-hom-cofork-equiv-double-arrow h _)) =
    coh-hom-cofork-hom-double-arrow c c' h
```
