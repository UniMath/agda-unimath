# Forks

```agda
module foundation.forks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.codiagonal-maps-of-types
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.contractible-types
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equality-cartesian-product-types
open import foundation.equality-of-equality-cartesian-product-types
open import foundation.equivalences
open import foundation.equivalences-cospan-diagrams
open import foundation.equivalences-double-arrows
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.morphisms-cospan-diagrams
open import foundation.morphisms-double-arrows
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.diagonal-maps-cartesian-products-of-types
```

</details>

## Idea

A {{#concept "fork" Disambiguation="of types" Agda=fork}} of a
[double arrow](foundation.double-arrows.md) `f, g : A → B` with vertext `X` is a
map `e : X → A` together with a [homotopy](foundation.homotopies.md)
`H : f ∘ e ~ g ∘ e`. The name comes from the diagram

```text
                g
      e      ------>
 X ------> A         B
             ------>
                f
```

which looks like a fork.

Forks are an analog of
[cones over cospan diagrams](foundation.cones-over-cospan-diagrams.md) for
double arrows. The universal fork of a double arrow is their
[equalizer](foundation.standard-equalizers.md).

## Definitions

### Forks

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2)
  where

  coherence-fork : {X : UU l3} → (X → domain-double-arrow a) → UU (l2 ⊔ l3)
  coherence-fork e =
    left-map-double-arrow a ∘ e ~
    right-map-double-arrow a ∘ e

  fork : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  fork X = Σ (X → domain-double-arrow a) (coherence-fork)

  module _
    {X : UU l3} (e : fork X)
    where

    map-fork : X → domain-double-arrow a
    map-fork = pr1 e

    coh-fork : coherence-fork map-fork
    coh-fork = pr2 e
```

### Homotopies of forks

A homotopy between forks with the same vertex is given by a homotopy between the
two maps, together with a coherence datum asserting that we may apply the given
homotopy and the appropriate fork homotopy in either order.

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  where

  coherence-htpy-fork :
    (e e' : fork a X) →
    (K : map-fork a e ~ map-fork a e') →
    UU (l2 ⊔ l3)
  coherence-htpy-fork e e' K =
    ( coh-fork a e ∙h right-map-double-arrow a ·l K) ~
    ( left-map-double-arrow a ·l K ∙h coh-fork a e')

  htpy-fork : fork a X → fork a X → UU (l1 ⊔ l2 ⊔ l3)
  htpy-fork e e' =
    Σ ( map-fork a e ~ map-fork a e')
      ( coherence-htpy-fork e e')
```

### Precomposing forks

Given a fork `e : X → A` and a map `h : X → Y`, we may compose the two to get a
new fork `e ∘ h`.

```text
                          g
      e         h      ------>
 Y ------> X ------> A         B
                       ------>
                          f
```

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : fork a X)
  where

  fork-map : {l : Level} {Y : UU l} → (Y → X) → fork a Y
  pr1 (fork-map h) = map-fork a e ∘ h
  pr2 (fork-map h) = coh-fork a e ·r h
```

## Properties

### Characterization of identity types of forks

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  where

  refl-htpy-fork : (e : fork a X) → htpy-fork a e e
  pr1 (refl-htpy-fork e) = refl-htpy
  pr2 (refl-htpy-fork e) = right-unit-htpy

  htpy-fork-eq :
    (e e' : fork a X) → (e ＝ e') → htpy-fork a e e'
  htpy-fork-eq e .e refl = refl-htpy-fork e

  abstract
    is-torsorial-htpy-fork :
      (e : fork a X) → is-torsorial (htpy-fork a e)
    is-torsorial-htpy-fork e =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-fork a e))
        ( map-fork a e , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( coherence-fork a (map-fork a e))
              ( λ K → coh-fork a e ~ K))
          ( tot (λ K M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv
            ( is-equiv-concat-htpy right-unit-htpy))
          ( is-torsorial-htpy (coh-fork a e)))

  abstract
    is-equiv-htpy-fork-eq :
      (e e' : fork a X) → is-equiv (htpy-fork-eq e e')
    is-equiv-htpy-fork-eq e =
      fundamental-theorem-id (is-torsorial-htpy-fork e) (htpy-fork-eq e)

  eq-htpy-fork : (e e' : fork a X) → htpy-fork a e e' → e ＝ e'
  eq-htpy-fork e e' = map-inv-is-equiv (is-equiv-htpy-fork-eq e e')
```

### Precomposing a fork by identity is the identity

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : fork a X)
  where

  fork-map-id : fork-map a e id ＝ e
  fork-map-id =
    eq-htpy-fork a
      ( fork-map a e id)
      ( e)
      ( ( refl-htpy) ,
        ( right-unit-htpy ∙h
          inv-left-unit-law-left-whisker-comp (coh-fork a e) ∙h
          left-unit-law-left-whisker-comp (coh-fork a e)))
```

### Precomposing forks distributes over function composition

```text
                                 g
      k        h        e      ----->
  Z -----> Y -----> X -----> A        B
                               ----->
                                 f
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (a : double-arrow l1 l2)
  {X : UU l3} {Y : UU l4} {Z : UU l5}
  (e : fork a X)
  where

  fork-map-comp :
    (h : Y → X) (k : Z → Y) →
    fork-map a e (h ∘ k) ＝ fork-map a (fork-map a e h) k
  fork-map-comp h k =
    eq-htpy-fork a
      ( fork-map a e (h ∘ k))
      ( fork-map a (fork-map a e h) k)
      ( refl-htpy , right-unit-htpy)
```

### Forks are special cases of cones over cospans

The type of forks of a double arrow `f, g : A → B` is equivalent to the type of
[cones](foundation.cones-over-cospan-diagrams.md) over the cospan

```text
       Δ           (f,g)
  B ------> B × B <------ A.
```

```agda
module _
  {l1 l2 : Level} (a@(A , B , f , g) : double-arrow l1 l2)
  where

  vertical-map-cospan-cone-fork :
    codomain-double-arrow a → codomain-double-arrow a × codomain-double-arrow a
  vertical-map-cospan-cone-fork = diagonal-product (codomain-double-arrow a)

  horizontal-map-cospan-cone-fork :
    domain-double-arrow a → codomain-double-arrow a × codomain-double-arrow a
  horizontal-map-cospan-cone-fork x =
    ( left-map-double-arrow a x , right-map-double-arrow a x)

  cospan-diagram-fork : cospan-diagram l1 l2 l2
  cospan-diagram-fork =
    make-cospan-diagram
      ( horizontal-map-cospan-cone-fork)
      ( vertical-map-cospan-cone-fork)

module _
  {l1 l2 l3 : Level} (a@(A , B , f , g) : double-arrow l1 l2) {X : UU l3}
  where

  fork-cone-diagonal :
    cone
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( X) →
    fork a X
  pr1 (fork-cone-diagonal (f' , g' , H)) = g'
  pr2 (fork-cone-diagonal (f' , g' , H)) = inv-htpy (pr1 ·l H) ∙h pr2 ·l H

  horizontal-map-cone-fork : fork a X → X → codomain-double-arrow a
  horizontal-map-cone-fork e = left-map-double-arrow a ∘ map-fork a e

  vertical-map-cone-fork : fork a X → X → domain-double-arrow a
  vertical-map-cone-fork e = map-fork a e

  coherence-square-cone-fork :
    (e : fork a X) →
    coherence-square-maps
      ( vertical-map-cone-fork e)
      ( horizontal-map-cone-fork e)
      ( horizontal-map-cospan-cone-fork a)
      ( vertical-map-cospan-cone-fork a)
  coherence-square-cone-fork e x = eq-pair refl (coh-fork a e x)

  cone-diagonal-fork :
    fork a X →
    cone
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( X)
  pr1 (cone-diagonal-fork e) = horizontal-map-cone-fork e
  pr1 (pr2 (cone-diagonal-fork e)) = vertical-map-cone-fork e
  pr2 (pr2 (cone-diagonal-fork e)) = coherence-square-cone-fork e

  abstract
    is-section-cone-diagonal-fork :
      fork-cone-diagonal ∘ cone-diagonal-fork ~ id
    is-section-cone-diagonal-fork e =
      eq-htpy-fork a
        ( fork-cone-diagonal (cone-diagonal-fork e))
        ( e)
        ( refl-htpy ,
          ( λ x →
            right-unit ∙
            ap-binary
              ( _∙_)
              ( ap inv (ap-pr1-ap-pair (coh-fork a e x)))
              ( ap-pr2-eq-pair refl (coh-fork a e x))))

  abstract
    is-retraction-cone-diagonal-fork' :
      id ~ cone-diagonal-fork ∘ fork-cone-diagonal
    is-retraction-cone-diagonal-fork' c@(f' , g' , H) =
      eq-htpy-cone
        ( vertical-map-cospan-cone-fork a)
        ( horizontal-map-cospan-cone-fork a)
        ( c)
        ( cone-diagonal-fork (fork-cone-diagonal c))
        ( pr1 ·l H ,
          refl-htpy ,
          λ x →
          eq-pair²
            ( ( equational-reasoning
                ap pr1 (H x ∙ refl)
                ＝ ap pr1 (H x) ∙ refl
                  by ap-concat pr1 (H x) refl
                ＝
                  ( ap pr1 (ap (diagonal-product B) (ap pr1 (H x)))) ∙
                  ( ap pr1
                    ( ap
                      ( left-map-double-arrow a (g' x) ,_)
                      ( inv (ap pr1 (H x)) ∙ ap pr2 (H x))))
                  by
                  ap-binary
                    ( _∙_)
                    ( inv-ap-id (ap pr1 (H x)) ∙
                      ap-comp pr1 (diagonal-product B) (ap pr1 (H x)))
                    ( inv-ap-pr1-ap-pair (inv (ap pr1 (H x)) ∙ ap pr2 (H x)))
                ＝
                  ap
                    ( pr1)
                    ( ap (diagonal-product B) (ap pr1 (H x)) ∙
                      ap
                        ( left-map-double-arrow a (g' x) ,_)
                        ( inv (ap pr1 (H x)) ∙ ap pr2 (H x)))
                  by
                  inv-ap-concat
                    ( pr1)
                    ( ap (diagonal-product B) (ap pr1 (H x)))
                    ( ap
                      ( left-map-double-arrow a (g' x) ,_)
                      ( inv (ap pr1 (H x)) ∙ ap pr2 (H x)))) ,
              ( equational-reasoning
                ap pr2 (H x ∙ refl)
                ＝ ap pr2 (H x)
                  by ap (ap pr2) right-unit
                ＝ ap pr1 (H x) ∙ (inv (ap pr1 (H x)) ∙ ap pr2 (H x))
                  by inv (is-section-inv-concat (ap pr1 (H x)) (ap pr2 (H x)))
                ＝ ap pr2 (ap (diagonal-product B) (ap pr1 (H x))) ∙
                  ap
                    ( pr2)
                    ( ap
                      ( left-map-double-arrow a (g' x) ,_)
                      ( inv (ap pr1 (H x)) ∙ ap pr2 (H x)))
                  by
                  ap-binary
                    ( _∙_)
                    ( ( inv-ap-id (ap pr1 (H x))) ∙
                      ( ap-comp pr2 (diagonal-product B) (ap pr1 (H x))))
                    ( inv-ap-pr2-ap-pair (inv (ap pr1 (H x)) ∙ ap pr2 (H x)))
                ＝
                  ( ap pr2
                    ( ( ap (diagonal-product B) (ap pr1 (H x))) ∙
                      ( ap
                        ( left-map-double-arrow a (g' x) ,_)
                        ( inv (ap pr1 (H x)) ∙ ap pr2 (H x)))))
                  by
                  inv-ap-concat
                    ( pr2)
                    ( ap (diagonal-product B) (ap pr1 (H x)))
                    ( ap
                      ( left-map-double-arrow a (g' x) ,_)
                      ( inv (ap pr1 (H x)) ∙ ap pr2 (H x))))))

    is-retraction-cone-diagonal-fork :
      cone-diagonal-fork ∘ fork-cone-diagonal ~ id
    is-retraction-cone-diagonal-fork =
      inv-htpy is-retraction-cone-diagonal-fork'

  is-equiv-fork-cone-diagonal :
    is-equiv fork-cone-diagonal
  is-equiv-fork-cone-diagonal =
    is-equiv-is-invertible
      ( cone-diagonal-fork)
      ( is-section-cone-diagonal-fork)
      ( is-retraction-cone-diagonal-fork)

  equiv-cone-diagonal-fork :
    cone
      ( vertical-map-cospan-cone-fork a)
      ( horizontal-map-cospan-cone-fork a)
      ( X) ≃
    fork a X
  pr1 equiv-cone-diagonal-fork = fork-cone-diagonal
  pr2 equiv-cone-diagonal-fork = is-equiv-fork-cone-diagonal

module _
  {l1 l2 : Level} (a@(A , B , f , g) : double-arrow l1 l2)
  where

  abstract
    triangle-fork-cone :
      {l3 l4 : Level} {X : UU l3} {Y : UU l4} →
      (e : fork a X) →
      coherence-triangle-maps
        ( fork-map a e {Y = Y})
        ( fork-cone-diagonal a)
        ( cone-map
          ( vertical-map-cospan-cone-fork a)
          ( horizontal-map-cospan-cone-fork a)
          ( cone-diagonal-fork a e))
    triangle-fork-cone e h =
      eq-htpy-fork a
        ( fork-map a e h)
        ( fork-cone-diagonal
          ( a)
          ( cone-map
            ( vertical-map-cospan-cone-fork a)
            ( horizontal-map-cospan-cone-fork a)
            ( cone-diagonal-fork a e)
            ( h)))
        ( refl-htpy ,
          λ x →
          equational-reasoning
            coh-fork a e (h x) ∙ refl
            ＝ coh-fork a e (h x) by right-unit
            ＝ inv
                ( ap
                  ( pr1)
                  ( ap
                    ( left-map-double-arrow a (map-fork a e (h x)) ,_)
                    ( coh-fork a e (h x)))) ∙
                ( ap
                    ( pr2)
                    ( ap
                      ( left-map-double-arrow a (map-fork a e (h x)) ,_)
                      ( coh-fork a e (h x))))
              by
              ap-binary
                ( _∙_)
                ( ap inv (inv-ap-pr1-ap-pair (coh-fork a e (h x))))
                ( inv-ap-pr2-ap-pair (coh-fork a e (h x))))
```

### Morphisms between double arrows induce morphisms between fork cospan diagrams

A [morphism of double arrows](foundation.morphisms-double-arrows.md)

```text
           i
     A --------> X
    | |         | |
  f | | g     h | | k
    | |         | |
    ∨ ∨         ∨ ∨
     B --------> Y
           j
```

induces a [morphism of cospan diagrams](foundation.morphisms-cospan-diagrams.md)

```text
        (f,g)             Δ
    A --------> B × B <-------- B
    |             |             |
  i |             | j × j       | j
    ∨             ∨             ∨
    X --------> Y × Y <-------- Y
        (h,k)             Δ
```

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  (h : hom-double-arrow a a')
  where

  cospanning-map-hom-cospan-diagram-fork-hom-double-arrow :
    codomain-double-arrow a × codomain-double-arrow a →
    codomain-double-arrow a' × codomain-double-arrow a'
  cospanning-map-hom-cospan-diagram-fork-hom-double-arrow =
    map-product
      ( codomain-map-hom-double-arrow a a' h)
      ( codomain-map-hom-double-arrow a a' h)

  left-square-hom-cospan-diagram-fork-hom-double-arrow :
    coherence-square-maps
      ( horizontal-map-cospan-cone-fork a)
      ( domain-map-hom-double-arrow a a' h)
      ( cospanning-map-hom-cospan-diagram-fork-hom-double-arrow)
      ( horizontal-map-cospan-cone-fork a')
  left-square-hom-cospan-diagram-fork-hom-double-arrow x =
    inv
      ( eq-pair
        ( left-square-hom-double-arrow a a' h x)
        ( right-square-hom-double-arrow a a' h x))

  right-square-hom-cospan-diagram-fork-hom-double-arrow :
    coherence-square-maps
        ( vertical-map-cospan-cone-fork a)
        ( codomain-map-hom-double-arrow a a' h)
        ( cospanning-map-hom-cospan-diagram-fork-hom-double-arrow)
        ( vertical-map-cospan-cone-fork a')
  right-square-hom-cospan-diagram-fork-hom-double-arrow = refl-htpy

  hom-cospan-diagram-fork-hom-double-arrow :
    hom-cospan-diagram (cospan-diagram-fork a) (cospan-diagram-fork a')
  pr1 hom-cospan-diagram-fork-hom-double-arrow =
    domain-map-hom-double-arrow a a' h
  pr1 (pr2 hom-cospan-diagram-fork-hom-double-arrow) =
    codomain-map-hom-double-arrow a a' h
  pr1 (pr2 (pr2 hom-cospan-diagram-fork-hom-double-arrow)) =
    cospanning-map-hom-cospan-diagram-fork-hom-double-arrow
  pr1 (pr2 (pr2 (pr2 hom-cospan-diagram-fork-hom-double-arrow))) =
    left-square-hom-cospan-diagram-fork-hom-double-arrow
  pr2 (pr2 (pr2 (pr2 hom-cospan-diagram-fork-hom-double-arrow))) =
    right-square-hom-cospan-diagram-fork-hom-double-arrow
```

### Equivalences between double arrows induce equivalences between fork cospan diagrams

An [equivalence of double arrows](foundation.equivalences-double-arrows.md)

```text
           i
     A --------> X
    | |    ≃    | |
  f | | g     h | | k
    | |         | |
    ∨ ∨    ≃    ∨ ∨
     B --------> Y
           j
```

induces an
[equivalence of cospan diagrams](foundation.equivalences-cospan-diagrams.md)

```text
        (f,g)             Δ
    A --------> B × B <-------- B
    |             |             |
  i | ≃         ≃ | j × j     ≃ | j
    ∨             ∨             ∨
    X --------> Y × Y <-------- Y
        (h,k)             Δ
```

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  (e : equiv-double-arrow a a')
  where

  cospanning-equiv-equiv-cospan-diagram-fork-equiv-double-arrow :
    codomain-double-arrow a × codomain-double-arrow a ≃
    codomain-double-arrow a' × codomain-double-arrow a'
  cospanning-equiv-equiv-cospan-diagram-fork-equiv-double-arrow =
    equiv-product
      ( codomain-equiv-equiv-double-arrow a a' e)
      ( codomain-equiv-equiv-double-arrow a a' e)

  left-square-equiv-cospan-diagram-fork-equiv-double-arrow :
    coherence-square-maps
      ( horizontal-map-cospan-cone-fork a)
      ( domain-map-equiv-double-arrow a a' e)
      ( map-equiv cospanning-equiv-equiv-cospan-diagram-fork-equiv-double-arrow)
      ( horizontal-map-cospan-cone-fork a')
  left-square-equiv-cospan-diagram-fork-equiv-double-arrow =
    left-square-hom-cospan-diagram-fork-hom-double-arrow a a'
      ( hom-equiv-double-arrow a a' e)

  right-square-equiv-cospan-diagram-fork-equiv-double-arrow :
    coherence-square-maps'
      ( vertical-map-cospan-cone-fork a)
      ( codomain-map-equiv-double-arrow a a' e)
      ( map-equiv cospanning-equiv-equiv-cospan-diagram-fork-equiv-double-arrow)
      ( vertical-map-cospan-cone-fork a')
  right-square-equiv-cospan-diagram-fork-equiv-double-arrow =
    right-square-hom-cospan-diagram-fork-hom-double-arrow a a'
      ( hom-equiv-double-arrow a a' e)

  equiv-cospan-diagram-fork-equiv-double-arrow :
    equiv-cospan-diagram (cospan-diagram-fork a) (cospan-diagram-fork a')
  pr1 equiv-cospan-diagram-fork-equiv-double-arrow =
    domain-equiv-equiv-double-arrow a a' e
  pr1 (pr2 equiv-cospan-diagram-fork-equiv-double-arrow) =
    codomain-equiv-equiv-double-arrow a a' e
  pr1 (pr2 (pr2 equiv-cospan-diagram-fork-equiv-double-arrow)) =
    cospanning-equiv-equiv-cospan-diagram-fork-equiv-double-arrow
  pr1 (pr2 (pr2 (pr2 equiv-cospan-diagram-fork-equiv-double-arrow))) =
    left-square-equiv-cospan-diagram-fork-equiv-double-arrow
  pr2 (pr2 (pr2 (pr2 equiv-cospan-diagram-fork-equiv-double-arrow))) =
    right-square-equiv-cospan-diagram-fork-equiv-double-arrow
```
