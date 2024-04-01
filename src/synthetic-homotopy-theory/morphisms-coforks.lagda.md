# Morphisms of coforks

```agda
module synthetic-homotopy-theory.morphisms-coforks where
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
{{#concept "morphism of coforks" Disambiguation="of types" Agda=hom-cofork}}
over `e` is a triple `(m, H, K)`, with `m : X → Y` a map of vertices of the
coforks, `H` a [homotopy](foundation-core.homotopies.md) witnessing that the
bottom square in

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
datum filling the inside --- we have two stacks of squares

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
`c'` filling the sides; that gives us the homotopies

```text
                                                i                 i
     A                  A                 A --------> U     A --------> U
     |                  |                             |                 |
   f |                f |                             | h               | k
     |                  |                             |                 |
     ∨                  ∨     j                       ∨                 ∨
     B         ~        B --------> V       ~         V        ~        V
     |                              |                 |                 |
   c |                              | c'              | c'              | c'
     |                              |                 |                 |
     ∨                              ∨                 ∨                 ∨
     X --------> Y                  Y                 Y                 Y
           m
```

and

```text
                                                                  i
     A                 A               A                    A --------> U
     |                 |               |                                |
   f |               g |             g |                                | k
     |                 |               |                                |
     ∨                 ∨               ∨     j                          ∨
     B         ~       B       ~       B --------> V           ~        V
     |                 |                           |                    |
   c |               c |                           | c'                 | c'
     |                 |                           |                    |
     ∨                 ∨                           ∨                    ∨
     X --------> Y     X --------> Y               Y                    Y ,
           m                 m
```

which we require to be homotopic.

## Definitions

### Morphisms of coforks

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : cofork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : cofork a' Y)
  (h : hom-double-arrow a a')
  where

  coherence-map-cofork-hom-cofork : (X → Y) → UU (l2 ⊔ l6)
  coherence-map-cofork-hom-cofork u =
    coherence-square-maps
      ( codomain-map-hom-double-arrow a a' h)
      ( map-cofork a c)
      ( map-cofork a' c')
      ( u)

  coherence-hom-cofork :
    (u : X → Y) → coherence-map-cofork-hom-cofork u →
    UU (l1 ⊔ l6)
  coherence-hom-cofork u H =
    ( ( H ·r (left-map-double-arrow a)) ∙h
      ( ( map-cofork a' c') ·l
        ( left-square-hom-double-arrow a a' h)) ∙h
      ( (coh-cofork a' c') ·r (domain-map-hom-double-arrow a a' h))) ~
    ( ( u ·l (coh-cofork a c)) ∙h
      ( H ·r (right-map-double-arrow a)) ∙h
      ( (map-cofork a' c') ·l (right-square-hom-double-arrow a a' h)))

  hom-cofork : UU (l1 ⊔ l2 ⊔ l3 ⊔ l6)
  hom-cofork =
    Σ ( X → Y)
      ( λ u →
        Σ ( coherence-map-cofork-hom-cofork u)
          ( coherence-hom-cofork u))

  module _
    (h' : hom-cofork)
    where

    map-hom-cofork : X → Y
    map-hom-cofork = pr1 h'

    coh-map-cofork-hom-cofork : coherence-map-cofork-hom-cofork map-hom-cofork
    coh-map-cofork-hom-cofork = pr1 (pr2 h')

    hom-map-cofork-hom-cofork :
      hom-arrow (map-cofork a c) (map-cofork a' c')
    pr1 hom-map-cofork-hom-cofork = codomain-map-hom-double-arrow a a' h
    pr1 (pr2 hom-map-cofork-hom-cofork) = map-hom-cofork
    pr2 (pr2 hom-map-cofork-hom-cofork) = coh-map-cofork-hom-cofork

    coh-map-cofork :
      coherence-hom-cofork map-hom-cofork coh-map-cofork-hom-cofork
    coh-map-cofork = pr2 (pr2 h')
```
