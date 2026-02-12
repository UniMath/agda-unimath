# Equivalences of forks over equivalences of double arrows

```agda
module foundation.equivalences-forks-over-equivalences-double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-ternary-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.double-arrows
open import foundation.equality-cartesian-product-types
open import foundation.equality-of-equality-cartesian-product-types
open import foundation.equivalences
open import foundation.action-on-identifications-binary-functions
open import foundation.equivalences-arrows
open import foundation.equivalences-double-arrows
open import foundation.forks
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
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
`e : (f, g) ≃ (h, k)`.

Then an
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
  pr1 (pr2 (equiv-hom-fork-equiv-double-arrow h is-equiv-map-fork)) =
    coh-map-fork-hom-fork-hom-double-arrow a a' c c'
      ( hom-equiv-double-arrow a a' e)
      ( h)
  pr2 (pr2 (equiv-hom-fork-equiv-double-arrow h is-equiv-map-fork)) =
    coh-hom-fork-hom-double-arrow a a' c c' (hom-equiv-double-arrow a a' e) h
```

### Coherence cube on cones induced by an equivalence of forks

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {a : double-arrow l1 l2} {X : UU l3} (c : fork a X)
  {a' : double-arrow l4 l5} {Y : UU l6} (c' : fork a' Y)
  (e : equiv-double-arrow a a') (e' : equiv-fork-equiv-double-arrow a a' c c' e)
  where

  coherence-cube-cone-fork-equiv-fork-equiv-double-arrow :
    coherence-cube-maps
      ( vertical-map-cospan-cone-fork a)
      ( codomain-map-equiv-double-arrow a a' e)
      ( map-equiv
        ( equiv-product
          ( codomain-equiv-equiv-double-arrow a a' e)
          ( codomain-equiv-equiv-double-arrow a a' e)))
      ( vertical-map-cospan-cone-fork a')
      ( vertical-map-cone-fork a c)
      ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
      ( domain-map-equiv-double-arrow a a' e)
      ( vertical-map-cone-fork a' c')
      ( horizontal-map-cone-fork a c)
      ( horizontal-map-cospan-cone-fork a)
      ( horizontal-map-cone-fork a' c')
      ( horizontal-map-cospan-cone-fork a')
      ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
      ( coherence-square-cone-fork a c)
      ( pasting-vertical-coherence-square-maps
        ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
        ( map-fork a c)
        ( map-fork a' c')
        ( domain-map-equiv-double-arrow a a' e)
        ( left-map-double-arrow a)
        ( left-map-double-arrow a')
        ( codomain-map-equiv-double-arrow a a' e)
        ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
        ( left-square-equiv-double-arrow a a' e))
      ( inv-htpy
        ( left-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e))
      ( coherence-square-cone-fork a' c')
      ( right-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e)
  coherence-cube-cone-fork-equiv-fork-equiv-double-arrow x =
    map-inv-equiv
      ( equiv-pair-eq² path-left-ev-fork-equiv path-right-ev-fork-equiv)
      ( pr1-coherence-cube-cone-fork-equiv-fork-equiv-double-arrow , pr2-coherence-cube-cone-fork-equiv-fork-equiv-double-arrow)
    where
      left-square-ev-fork-equiv :
        codomain-map-equiv-double-arrow a a' e
          ( left-map-double-arrow a (map-fork a c x)) ＝
        left-map-double-arrow a'
          ( domain-map-equiv-double-arrow a a' e (map-fork a c x))
      left-square-ev-fork-equiv =
        left-square-equiv-double-arrow a a' e (map-fork a c x)

      right-square-ev-fork-equiv :
        codomain-map-equiv-double-arrow a a' e
          ( right-map-double-arrow a (map-fork a c x)) ＝
        right-map-double-arrow a'
          ( domain-map-equiv-double-arrow a a' e
            (map-fork a c x))
      right-square-ev-fork-equiv =
        right-square-equiv-double-arrow a a' e (map-fork a c x)

      pasting-left-square-ev-fork-equiv :
        left-square-ev-fork-equiv ∙
        ap
          ( left-map-double-arrow a')
          ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e' x) ＝
        pasting-vertical-coherence-square-maps
          ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
          ( map-fork a c)
          ( map-fork a' c')
          ( domain-map-equiv-double-arrow a a' e)
          ( left-map-double-arrow a)
          ( left-map-double-arrow a')
          ( codomain-map-equiv-double-arrow a a' e)
          ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
          ( left-square-equiv-double-arrow a a' e)
          x
      pasting-left-square-ev-fork-equiv = refl

      path-source-cone-square-ev-fork-equiv :
        map-equiv
          ( equiv-product
            ( codomain-equiv-equiv-double-arrow a a' e)
            ( codomain-equiv-equiv-double-arrow a a' e))
          ( vertical-map-cospan-cone-fork a
            ( horizontal-map-cone-fork a c x)) ＝
        map-equiv
          ( equiv-product
            ( codomain-equiv-equiv-double-arrow a a' e)
            ( codomain-equiv-equiv-double-arrow a a' e))
          ( horizontal-map-cospan-cone-fork a
            ( vertical-map-cone-fork a c x))
      path-source-cone-square-ev-fork-equiv =
        ap
          ( map-equiv
            ( equiv-product
              ( codomain-equiv-equiv-double-arrow a a' e)
              ( codomain-equiv-equiv-double-arrow a a' e)))
          ( coherence-square-cone-fork a c x)

      path-left-cospan-square-ev-fork-equiv :
        map-equiv
          ( cospanning-equiv-equiv-cospan-diagram-fork-equiv-double-arrow a a' e)
          ( horizontal-map-cospan-cone-fork a
            ( map-fork a c x)) ＝
        horizontal-map-cospan-cone-fork a'
          ( domain-map-equiv-double-arrow a a' e
            ( map-fork a c x))
      path-left-cospan-square-ev-fork-equiv =
        inv-htpy
          ( left-square-equiv-cospan-diagram-fork-equiv-double-arrow a a' e)
          ( map-fork a c x)

      path-map-coherence-ev-fork-equiv :
        horizontal-map-cospan-cone-fork a'
          ( domain-map-equiv-double-arrow a a' e
            ( map-fork a c x)) ＝
        horizontal-map-cospan-cone-fork a'
          ( map-fork a' c'
            ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x))
      path-map-coherence-ev-fork-equiv =
        ap (horizontal-map-cospan-cone-fork a')
          ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e' x)

      path-left-pasting-square-ev-fork-equiv :
        vertical-map-cospan-cone-fork a'
          ( codomain-map-equiv-double-arrow a a' e
            ( left-map-double-arrow a
              ( map-fork a c x))) ＝
        vertical-map-cospan-cone-fork a'
          ( left-map-double-arrow a'
            ( map-fork a' c'
              ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x)))
      path-left-pasting-square-ev-fork-equiv =
        ap
          ( vertical-map-cospan-cone-fork a')
          ( pasting-vertical-coherence-square-maps
            ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
            ( map-fork a c)
            ( map-fork a' c')
            ( domain-map-equiv-double-arrow a a' e)
            ( left-map-double-arrow a)
            ( left-map-double-arrow a')
            ( codomain-map-equiv-double-arrow a a' e)
              ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
              ( left-square-equiv-double-arrow a a' e)
              x)

      path-target-cone-square-ev-fork-equiv :
        vertical-map-cospan-cone-fork a'
          ( left-map-double-arrow a'
            ( map-fork a' c'
              ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x))) ＝
        horizontal-map-cospan-cone-fork a'
          ( map-fork a' c'
            ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x))
      path-target-cone-square-ev-fork-equiv =
        coherence-square-cone-fork a' c'
          ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x)

      path-left-ev-fork-equiv :
        map-equiv
          ( equiv-product
            ( codomain-equiv-equiv-double-arrow a a' e)
            ( codomain-equiv-equiv-double-arrow a a' e))
          ( vertical-map-cospan-cone-fork a
            ( horizontal-map-cone-fork a c x)) ＝
        horizontal-map-cospan-cone-fork a'
          ( map-fork a' c' (map-equiv-fork-equiv-double-arrow a a' c c' e e' x))
      path-left-ev-fork-equiv =
        path-source-cone-square-ev-fork-equiv ∙
        path-left-cospan-square-ev-fork-equiv ∙
        path-map-coherence-ev-fork-equiv

      path-right-ev-fork-equiv :
        map-equiv
          ( equiv-product
            ( codomain-equiv-equiv-double-arrow a a' e)
            ( codomain-equiv-equiv-double-arrow a a' e))
          ( vertical-map-cospan-cone-fork a
            ( horizontal-map-cone-fork a c x)) ＝
        horizontal-map-cospan-cone-fork a'
          ( map-fork a' c'
            ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x))
      path-right-ev-fork-equiv =
        path-left-pasting-square-ev-fork-equiv ∙
        path-target-cone-square-ev-fork-equiv

      ap-pr1-path-source-cone-square-ev-fork-equiv :
        ap pr1 path-source-cone-square-ev-fork-equiv ＝ refl
      ap-pr1-path-source-cone-square-ev-fork-equiv =
        ( inv-ap-comp
          ( pr1)
          ( map-equiv
            ( equiv-product
              ( codomain-equiv-equiv-double-arrow a a' e)
              ( codomain-equiv-equiv-double-arrow a a' e)))
          ( coherence-square-cone-fork a c x)) ∙
        ( ap-comp
          ( codomain-map-equiv-double-arrow a a' e)
          ( pr1)
          ( coherence-square-cone-fork a c x)) ∙
        ( ap
          ( ap (codomain-map-equiv-double-arrow a a' e))
          ( ap-pr1-ap-pair (coh-fork a c x)))

      ap-pr2-path-source-cone-square-ev-fork-equiv :
        ap pr2 path-source-cone-square-ev-fork-equiv ＝
        ap (codomain-map-equiv-double-arrow a a' e) (coh-fork a c x)
      ap-pr2-path-source-cone-square-ev-fork-equiv =
        ( inv-ap-comp
          ( pr2)
          ( map-equiv
            ( equiv-product
              ( codomain-equiv-equiv-double-arrow a a' e)
              ( codomain-equiv-equiv-double-arrow a a' e)))
          ( coherence-square-cone-fork a c x)) ∙
        ( ap-comp
          ( codomain-map-equiv-double-arrow a a' e)
          ( pr2)
          ( coherence-square-cone-fork a c x)) ∙
        ( ap
          ( ap (codomain-map-equiv-double-arrow a a' e))
          ( ap-pr2-ap-pair (coh-fork a c x)))

      ap-pr1-path-left-cospan-square-ev-fork-equiv :
        ap pr1 path-left-cospan-square-ev-fork-equiv ＝ left-square-ev-fork-equiv
      ap-pr1-path-left-cospan-square-ev-fork-equiv =
        ( ap
          ( ap pr1)
          ( inv-inv
            ( eq-pair left-square-ev-fork-equiv right-square-ev-fork-equiv)) ∙
          ap-pr1-eq-pair
            ( left-square-ev-fork-equiv)
            ( right-square-ev-fork-equiv))

      ap-pr2-path-left-cospan-square-ev-fork-equiv :
        ap pr2 path-left-cospan-square-ev-fork-equiv ＝ right-square-ev-fork-equiv
      ap-pr2-path-left-cospan-square-ev-fork-equiv =
        ( ap (ap pr2)
          ( inv-inv
            ( eq-pair left-square-ev-fork-equiv right-square-ev-fork-equiv)) ∙
          ap-pr2-eq-pair
            left-square-ev-fork-equiv
            right-square-ev-fork-equiv)

      ap-pr1-path-left-pasting-square-ev-fork-equiv :
        ap pr1 path-left-pasting-square-ev-fork-equiv ＝
        pasting-vertical-coherence-square-maps
          ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
          ( map-fork a c)
          ( map-fork a' c')
          ( domain-map-equiv-double-arrow a a' e)
          ( left-map-double-arrow a)
          ( left-map-double-arrow a')
          ( codomain-map-equiv-double-arrow a a' e)
          ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
          ( left-square-equiv-double-arrow a a' e)
          ( x)
      ap-pr1-path-left-pasting-square-ev-fork-equiv =
        inv (inv-ap-id P ∙ ap-comp pr1 (vertical-map-cospan-cone-fork a') P)
        where
          P =
            pasting-vertical-coherence-square-maps
              ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
              ( map-fork a c)
              ( map-fork a' c')
              ( domain-map-equiv-double-arrow a a' e)
              ( left-map-double-arrow a)
              ( left-map-double-arrow a')
              ( codomain-map-equiv-double-arrow a a' e)
              ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
              ( left-square-equiv-double-arrow a a' e)
              ( x)

      ap-pr2-path-left-pasting-square-ev-fork-equiv :
        ap pr2 path-left-pasting-square-ev-fork-equiv ＝
        pasting-vertical-coherence-square-maps
          ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
          ( map-fork a c)
          ( map-fork a' c')
          ( domain-map-equiv-double-arrow a a' e)
          ( left-map-double-arrow a)
          ( left-map-double-arrow a')
          ( codomain-map-equiv-double-arrow a a' e)
          ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
          ( left-square-equiv-double-arrow a a' e)
          ( x)
      ap-pr2-path-left-pasting-square-ev-fork-equiv =
        inv (inv-ap-id P ∙ ap-comp pr2 (vertical-map-cospan-cone-fork a') P)
        where
          P =
            pasting-vertical-coherence-square-maps
              ( map-equiv-fork-equiv-double-arrow a a' c c' e e')
              ( map-fork a c)
              ( map-fork a' c')
              ( domain-map-equiv-double-arrow a a' e)
              ( left-map-double-arrow a)
              ( left-map-double-arrow a')
              ( codomain-map-equiv-double-arrow a a' e)
              ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e')
              ( left-square-equiv-double-arrow a a' e)
              ( x)

      pr1-coherence-cube-cone-fork-equiv-fork-equiv-double-arrow :
        pr1 (pair-eq path-left-ev-fork-equiv) ＝
        pr1 (pair-eq path-right-ev-fork-equiv)
      pr1-coherence-cube-cone-fork-equiv-fork-equiv-double-arrow =
        ( ap-concat
          ( pr1)
          ( ( path-source-cone-square-ev-fork-equiv) ∙
            ( path-left-cospan-square-ev-fork-equiv))
          ( path-map-coherence-ev-fork-equiv)) ∙
        ( ap-binary
          ( _∙_)
          ( ( ap-concat
              ( pr1)
              ( path-source-cone-square-ev-fork-equiv)
              ( path-left-cospan-square-ev-fork-equiv)) ∙
            ( ap
              ( _∙ ap pr1 path-left-cospan-square-ev-fork-equiv)
              ( ap-pr1-path-source-cone-square-ev-fork-equiv) ∙
            ( ap-pr1-path-left-cospan-square-ev-fork-equiv)))
          ( inv-ap-comp
            ( pr1)
            ( horizontal-map-cospan-cone-fork a')
            ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e' x))) ∙
        ( inv pasting-left-square-ev-fork-equiv) ∙
        ( inv ap-pr1-path-left-pasting-square-ev-fork-equiv) ∙
        ( inv right-unit) ∙
        ( ap
          ( ap pr1 path-left-pasting-square-ev-fork-equiv ∙_)
          ( inv
            ( ap-pr1-ap-pair
              ( coh-fork a' c'
                ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x))))) ∙
        ( inv-ap-concat
          ( pr1)
          ( path-left-pasting-square-ev-fork-equiv)
          ( path-target-cone-square-ev-fork-equiv))

      pr2-coherence-cube-cone-fork-equiv-fork-equiv-double-arrow :
        pr2 (pair-eq path-left-ev-fork-equiv) ＝
        pr2 (pair-eq path-right-ev-fork-equiv)
      pr2-coherence-cube-cone-fork-equiv-fork-equiv-double-arrow =
        ap-concat
          ( pr2)
          ( ( path-source-cone-square-ev-fork-equiv) ∙
            ( path-left-cospan-square-ev-fork-equiv))
          ( path-map-coherence-ev-fork-equiv) ∙
        ( ap-binary
          ( _∙_)
          ( ( ap-concat
              ( pr2)
              ( path-source-cone-square-ev-fork-equiv)
              ( path-left-cospan-square-ev-fork-equiv)) ∙
            ( ap-binary
              ( _∙_)
              ( ap-pr2-path-source-cone-square-ev-fork-equiv)
              ( ap-pr2-path-left-cospan-square-ev-fork-equiv)))
          ( inv-ap-comp
            ( pr2)
            ( horizontal-map-cospan-cone-fork a')
            ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e' x))) ∙
        ( assoc
          ( ap (codomain-map-equiv-double-arrow a a' e) (coh-fork a c x))
          ( right-square-ev-fork-equiv)
          ( ap
            ( right-map-double-arrow a')
            (coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e' x))) ∙
        ( inv (coh-equiv-fork-equiv-double-arrow a a' c c' e e' x)) ∙
        ( inv
          ( assoc
            ( left-square-ev-fork-equiv)
            ( ap
              ( left-map-double-arrow a')
              ( coh-map-fork-equiv-fork-equiv-double-arrow a a' c c' e e' x))
            ( coh-fork a' c'
              ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x)))) ∙
        ( ap-binary (_∙_)
          ( ( inv pasting-left-square-ev-fork-equiv) ∙
            ( inv ap-pr2-path-left-pasting-square-ev-fork-equiv))
          ( inv
            (ap-pr2-ap-pair
              ( coh-fork a' c'
                ( map-equiv-fork-equiv-double-arrow a a' c c' e e' x))))) ∙
        ( inv-ap-concat
          ( pr2)
          ( path-left-pasting-square-ev-fork-equiv)
          ( path-target-cone-square-ev-fork-equiv))
```
