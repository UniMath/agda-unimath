# Functoriality of the action on identifications of functions

```agda
module foundation.functoriality-action-on-identifications-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-morphisms-arrows
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.homotopies-morphisms-arrows
open import foundation.morphisms-arrows
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-homotopies
open import foundation-core.commuting-squares-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
```

</details>

## Idea

Any [morphism of arrows](foundation.morphisms-arrows.md) `(i , j , H)` from `f`
to `g`

```text
        i
    A -----> X
    |        |
  f |        | g
    ∨        ∨
    B -----> Y
        j
```

induces a morphism of arrows between the
[action on identifications](foundation-core.fibers-of-maps.md) of `f` and `g`,
i.e., a [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
               ap j
    (x ＝ y) -------> (j x ＝ j y)
       |                   |
  ap f |                   | ap g
       ∨                   ∨
  (f x ＝ f y) -> (g (j x) ＝ g (j y)).
```

This operation from morphisms of arrows from `f` to `g` to morphisms of arrows
between their actions on identifications is the **functorial action of the
action on identifications of functions**. The functorial action obeys the
functor laws, i.e., it preserves identity morphisms and composition.

## Definitions

### Morphisms of arrows give morphisms of actions on identifications

A morphism of arrows `α : f → g` gives a morphism of actions on identifications
`ap-hom-arrow α : ap f → ap g`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) {x y : A}
  where

  map-domain-ap-hom-arrow :
    x ＝ y → map-domain-hom-arrow f g α x ＝ map-domain-hom-arrow f g α y
  map-domain-ap-hom-arrow = ap (map-domain-hom-arrow f g α)

  map-codomain-ap-hom-arrow :
    f x ＝ f y →
    g (map-domain-hom-arrow f g α x) ＝ g (map-domain-hom-arrow f g α y)
  map-codomain-ap-hom-arrow p =
    ( inv (coh-hom-arrow f g α x)) ∙
    ( ( ap (map-codomain-hom-arrow f g α) p) ∙
      ( coh-hom-arrow f g α y))

  inv-nat-coh-hom-arrow' :
    (p : x ＝ y) →
    coh-hom-arrow f g α x ∙ ap g (ap (map-domain-hom-arrow f g α) p) ＝
    ap (map-codomain-hom-arrow f g α) (ap f p) ∙ coh-hom-arrow f g α y
  inv-nat-coh-hom-arrow' p =
    ( inv
      ( ap
        ( coh-hom-arrow f g α x ∙_)
        ( ap-comp g (map-domain-hom-arrow f g α) p))) ∙
    ( ( nat-htpy (coh-hom-arrow f g α) p) ∙
      ( ap
        ( _∙ coh-hom-arrow f g α y)
        ( ap-comp (map-codomain-hom-arrow f g α) f p)))

  coh-ap-hom-arrow :
    (p : x ＝ y) →
    ( ( inv (coh-hom-arrow f g α x)) ∙
      ( ap (map-codomain-hom-arrow f g α) (ap f p) ∙ coh-hom-arrow f g α y)) ＝
    ( ap g (ap (map-domain-hom-arrow f g α) p))
  coh-ap-hom-arrow refl = left-inv (coh-hom-arrow f g α x)
```

Note that the coherence `coh-ap-hom-arrow` is defined by pattern matching due to
computational considerations, but we could have constructed it as the following
equality:

```text
  coh-ap-hom-arrow p =
    inv
      ( left-transpose-eq-concat
        ( coh-hom-arrow f g α x)
        ( ap g (ap (map-domain-hom-arrow f g α) p))
        ( ap (map-codomain-hom-arrow f g α) (ap f p) ∙ coh-hom-arrow f g α y)
        ( inv-nat-coh-hom-arrow' p))
```

```agda
  ap-hom-arrow :
    hom-arrow
      ( ap f {x} {y})
      ( ap g {map-domain-hom-arrow f g α x} {map-domain-hom-arrow f g α y})
  pr1 ap-hom-arrow = map-domain-ap-hom-arrow
  pr1 (pr2 ap-hom-arrow) = map-codomain-ap-hom-arrow
  pr2 (pr2 ap-hom-arrow) = coh-ap-hom-arrow
```

## Properties

### The functorial action of `ap` preserves the identity function

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A}
  where

  preserves-id-map-domain-ap-hom-arrow :
    map-domain-ap-hom-arrow f f id-hom-arrow {x} {y} ~ id
  preserves-id-map-domain-ap-hom-arrow = ap-id

  preserves-id-map-codomain-ap-hom-arrow :
    map-codomain-ap-hom-arrow f f id-hom-arrow {x} {y} ~ id
  preserves-id-map-codomain-ap-hom-arrow p = right-unit ∙ ap-id p

  coh-preserves-id-ap-hom-arrow :
    coherence-htpy-hom-arrow
      ( ap f)
      ( ap f)
      ( ap-hom-arrow f f id-hom-arrow)
      ( id-hom-arrow)
      ( preserves-id-map-domain-ap-hom-arrow)
      ( preserves-id-map-codomain-ap-hom-arrow)
  coh-preserves-id-ap-hom-arrow refl = refl

  preserves-id-ap-hom-arrow :
    htpy-hom-arrow
      ( ap f)
      ( ap f)
      ( ap-hom-arrow f f id-hom-arrow)
      ( id-hom-arrow)
  pr1 preserves-id-ap-hom-arrow = preserves-id-map-domain-ap-hom-arrow
  pr1 (pr2 preserves-id-ap-hom-arrow) = preserves-id-map-codomain-ap-hom-arrow
  pr2 (pr2 preserves-id-ap-hom-arrow) = coh-preserves-id-ap-hom-arrow
```

### For any `f : A → B` and any identification `p : b ＝ b'` in `B`, we obtain a morphism of arrows between the fiber inclusion at `b` to the fiber inclusion at `b'`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  tr-ap-hom-arrow :
    {x x' : A} (p : x' ＝ x) {y y' : A} (q : y ＝ y') →
    hom-arrow (ap f {x} {y}) (ap f {x'} {y'})
  pr1 (tr-ap-hom-arrow p q) r =
    p ∙ (r ∙ q)
  pr1 (pr2 (tr-ap-hom-arrow p q)) r =
    ap f p ∙ (r ∙ ap f q)
  pr2 (pr2 (tr-ap-hom-arrow p q)) r =
    inv (ap-concat f p (r ∙ q) ∙ ap (ap f p ∙_) (ap-concat f r q))
```

### The functorial action of `fiber` preserves composition of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V) (β : hom-arrow g h) (α : hom-arrow f g)
  {x y : A}
  where

  preserves-comp-map-domain-ap-hom-arrow :
    map-domain-ap-hom-arrow f h (comp-hom-arrow f g h β α) {x} {y} ~
    map-domain-ap-hom-arrow g h β ∘ map-domain-ap-hom-arrow f g α
  preserves-comp-map-domain-ap-hom-arrow =
    ap-comp (map-domain-hom-arrow g h β) (map-domain-hom-arrow f g α)

  preserves-comp-map-codomain-ap-hom-arrow :
    map-codomain-ap-hom-arrow f h (comp-hom-arrow f g h β α) {x} {y} ~
    map-codomain-ap-hom-arrow g h β ∘ map-codomain-ap-hom-arrow f g α
  preserves-comp-map-codomain-ap-hom-arrow p =
    ( ap
      ( _∙
        ( ( ap
            ( map-codomain-hom-arrow g h β ∘ map-codomain-hom-arrow f g α)
            ( p)) ∙
          ( ( ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α y)) ∙
            ( coh-hom-arrow g h β (map-domain-hom-arrow f g α y)))))
      ( distributive-inv-concat
        ( ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α x))
        ( coh-hom-arrow g h β (map-domain-hom-arrow f g α x)))) ∙
    ( assoc
      ( inv (coh-hom-arrow g h β (map-domain-hom-arrow f g α x)))
      ( inv (ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α x)))
      ( ap
        ( map-codomain-hom-arrow g h β ∘ map-codomain-hom-arrow f g α)
        ( p) ∙
        ( ap
          ( map-codomain-hom-arrow g h β)
          ( coh-hom-arrow f g α y) ∙
          coh-hom-arrow g h β (map-domain-hom-arrow f g α y)))) ∙
    ( ap
      ( inv (coh-hom-arrow g h β (map-domain-hom-arrow f g α x)) ∙_)
      ( inv
        ( assoc??²
          ( inv (ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α x)))
          ( ap (map-codomain-hom-arrow g h β ∘ map-codomain-hom-arrow f g α) p)
          ( ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α y))
          ( coh-hom-arrow g h β (map-domain-hom-arrow f g α y))) ∙
        ( ap
          ( _∙ coh-hom-arrow g h β (map-domain-hom-arrow f g α y))
          ( ap-binary (_∙_)
            ( inv
              ( ap-inv (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α x)))
            ( ap
              ( _∙ ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α y))
              ( ap-comp
                ( map-codomain-hom-arrow g h β)
                ( map-codomain-hom-arrow f g α) p) ∙
              ( inv
                ( ap-concat
                  ( map-codomain-hom-arrow g h β)
                  ( ap (map-codomain-hom-arrow f g α) p)
                  ( coh-hom-arrow f g α y)))) ∙
            ( inv
              ( ap-concat
                ( map-codomain-hom-arrow g h β)
                ( inv (coh-hom-arrow f g α x))
                ( ( ap (map-codomain-hom-arrow f g α) p) ∙
                  ( coh-hom-arrow f g α y))))))))
```

It remains to show that these homotopies are coherent.

### The functorial action of `ap` preserves homotopies of morphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α β : hom-arrow f g) {x y : A}
  where

  ap-htpy-hom-arrow' :
    htpy-hom-arrow f g α β →
    coherence-triangle-hom-arrow
      ( ap f)
      ( ap g {map-domain-hom-arrow f g α x} {map-domain-hom-arrow f g α y})
      ( ap g {map-domain-hom-arrow f g β x} {map-domain-hom-arrow f g β y})
      ( ap-hom-arrow f g β {x} {y})
      {!    !}
      ( ap-hom-arrow f g α {x} {y})
  ap-htpy-hom-arrow' = {!   !}
```
