# Morphisms of coforks under morphisms of double arrows

```agda
module synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.morphisms-double-arrows
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.coforks
```

</details>

## Idea

Consider two [double arrows](foundation.double-arrows.md) `f, g : A → B` and
`h, k : U → V`, equipped with [coforks](synthetic-homotopy-theory.coforks.md)
`c : B → X` and `c' : V → Y`, respectively, and a
[morphism of double arrows](foundation.morphisms-double-arrows.md)
`e : (f, g) → (h, k)`.

Then a
{{#concept "morphism of coforks" Disambiguation="under a morphism of double arrows" Agda=hom-cofork-hom-double-arrow}}
under `e` is a triple `(m, H, K)`, with `m : X → Y` a map of vertices of the
coforks, `H` a [homotopy](foundation-core.homotopies.md) witnessing that the
bottom square in the diagram

```text
           i
     A --------> U
    | |         | |
  f | | g     h | | k
    | |         | |
    ∨ ∨         ∨ ∨
     B --------> V
     |     j     |
   c |           | c'
     |           |
     ∨           ∨
     X --------> Y
           m
```

[commutes](foundation-core.commuting-squares-of-maps.md), and `K` a coherence
datum "filling the inside" --- we have two stacks of squares

```text
           i                        i
     A --------> U            A --------> U
     |           |            |           |
   f |           | h        g |           | k
     |           |            |           |
     ∨           ∨            ∨           ∨
     B --------> V            B --------> V
     |     j     |            |     j     |
   c |           | c'       c |           | c'
     |           |            |           |
     ∨           ∨            ∨           ∨
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

### Morphisms of coforks under morphisms of double arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  (h : hom-double-arrow a a')
  where

  coherence-map-cofork-hom-cofork-hom-double-arrow : (X → Y) → UU (l2 ⊔ l6)
  coherence-map-cofork-hom-cofork-hom-double-arrow u =
    coherence-square-maps
      ( codomain-map-hom-double-arrow a a' h)
      ( map-cofork a c)
      ( map-cofork a' c')
      ( u)

  coherence-hom-cofork-hom-double-arrow :
    (u : X → Y) → coherence-map-cofork-hom-cofork-hom-double-arrow u →
    UU (l1 ⊔ l6)
  coherence-hom-cofork-hom-double-arrow u H =
    ( ( H ·r (left-map-double-arrow a)) ∙h
      ( ( map-cofork a' c') ·l
        ( left-square-hom-double-arrow a a' h)) ∙h
      ( (coh-cofork a' c') ·r (domain-map-hom-double-arrow a a' h))) ~
    ( ( u ·l (coh-cofork a c)) ∙h
      ( H ·r (right-map-double-arrow a)) ∙h
      ( (map-cofork a' c') ·l (right-square-hom-double-arrow a a' h)))

  hom-cofork-hom-double-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l6)
  hom-cofork-hom-double-arrow =
    Σ ( X → Y)
      ( λ u →
        Σ ( coherence-map-cofork-hom-cofork-hom-double-arrow u)
          ( coherence-hom-cofork-hom-double-arrow u))
```

### Components of a morphism of coforks under a morphism of double arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  {h : hom-double-arrow a a'} (m : hom-cofork-hom-double-arrow c c' h)
  where

  map-hom-cofork-hom-double-arrow : X → Y
  map-hom-cofork-hom-double-arrow = pr1 m

  coh-map-cofork-hom-cofork-hom-double-arrow :
    coherence-map-cofork-hom-cofork-hom-double-arrow c c' h
      ( map-hom-cofork-hom-double-arrow)
  coh-map-cofork-hom-cofork-hom-double-arrow = pr1 (pr2 m)

  hom-map-cofork-hom-cofork-hom-double-arrow :
    hom-arrow (map-cofork a c) (map-cofork a' c')
  pr1 hom-map-cofork-hom-cofork-hom-double-arrow =
    codomain-map-hom-double-arrow a a' h
  pr1 (pr2 hom-map-cofork-hom-cofork-hom-double-arrow) =
    map-hom-cofork-hom-double-arrow
  pr2 (pr2 hom-map-cofork-hom-cofork-hom-double-arrow) =
    coh-map-cofork-hom-cofork-hom-double-arrow

  coh-hom-cofork-hom-double-arrow :
    coherence-hom-cofork-hom-double-arrow c c' h
      ( map-hom-cofork-hom-double-arrow)
      ( coh-map-cofork-hom-cofork-hom-double-arrow)
  coh-hom-cofork-hom-double-arrow = pr2 (pr2 m)
```
