# Equivalences of coforks

```agda
module synthetic-homotopy-theory.equivalences-coforks where
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
open import synthetic-homotopy-theory.morphisms-coforks
```

</details>

## Idea

Consider two [double arrows](foundation.double-arrows.md) `f, g : A → B` and
`h, k : U → V`, equipped with [coforks](synthetic-homotopy-theory.coforks.md)
`c : B → X` and `c' : V → Y`, respectively, and an
[equivalence of double arrows](foundation.equivalences-double-arrows.md)
`e : (f, g) ≃ (h, k)`.

Then an
{{#concept "equivalence of coforks" Disambiguation="of types" Agda=equiv-cofork}}
over `e` is a triple `(m, H, K)`, with `m : X ≃ Y` an
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

  coherence-map-cofork-equiv-cofork : (X ≃ Y) → UU (l2 ⊔ l6)
  coherence-map-cofork-equiv-cofork m =
    coherence-square-maps
      ( codomain-map-equiv-double-arrow a a' e)
      ( map-cofork a c)
      ( map-cofork a' c')
      ( map-equiv m)

  coherence-equiv-cofork :
    (m : X ≃ Y) → coherence-map-cofork-equiv-cofork m →
    UU (l1 ⊔ l6)
  coherence-equiv-cofork m H =
    ( ( H ·r (left-map-double-arrow a)) ∙h
      ( ( map-cofork a' c') ·l
        ( left-square-equiv-double-arrow a a' e)) ∙h
      ( (coh-cofork a' c') ·r (domain-map-equiv-double-arrow a a' e))) ~
    ( ( (map-equiv m) ·l (coh-cofork a c)) ∙h
      ( H ·r (right-map-double-arrow a)) ∙h
      ( (map-cofork a' c') ·l (right-square-equiv-double-arrow a a' e)))

  equiv-cofork : UU (l1 ⊔ l2 ⊔ l3 ⊔ l6)
  equiv-cofork =
    Σ ( X ≃ Y)
      ( λ m →
        Σ ( coherence-map-cofork-equiv-cofork m)
          ( coherence-equiv-cofork m))

  module _
    (e' : equiv-cofork)
    where

    equiv-equiv-cofork : X ≃ Y
    equiv-equiv-cofork = pr1 e'

    map-equiv-cofork : X → Y
    map-equiv-cofork = map-equiv equiv-equiv-cofork

    is-equiv-map-equiv-cofork : is-equiv map-equiv-cofork
    is-equiv-map-equiv-cofork =
      is-equiv-map-equiv equiv-equiv-cofork

    coh-map-cofork-equiv-cofork :
      coherence-map-cofork-equiv-cofork equiv-equiv-cofork
    coh-map-cofork-equiv-cofork = pr1 (pr2 e')

    equiv-map-cofork-equiv-cofork :
      equiv-arrow (map-cofork a c) (map-cofork a' c')
    pr1 equiv-map-cofork-equiv-cofork = codomain-equiv-equiv-double-arrow a a' e
    pr1 (pr2 equiv-map-cofork-equiv-cofork) = equiv-equiv-cofork
    pr2 (pr2 equiv-map-cofork-equiv-cofork) = coh-map-cofork-equiv-cofork

    hom-map-cofork-equiv-cofork :
      hom-arrow (map-cofork a c) (map-cofork a' c')
    hom-map-cofork-equiv-cofork =
      hom-equiv-arrow
        ( map-cofork a c)
        ( map-cofork a' c')
        ( equiv-map-cofork-equiv-cofork)

    coh-equiv-cofork :
      coherence-equiv-cofork equiv-equiv-cofork coh-map-cofork-equiv-cofork
    coh-equiv-cofork = pr2 (pr2 e')

    hom-cofork-equiv-cofork :
      hom-cofork c c' (hom-double-arrow-equiv-double-arrow a a' e)
    pr1 hom-cofork-equiv-cofork = map-equiv-cofork
    pr1 (pr2 hom-cofork-equiv-cofork) = coh-map-cofork-equiv-cofork
    pr2 (pr2 hom-cofork-equiv-cofork) = coh-equiv-cofork
```
