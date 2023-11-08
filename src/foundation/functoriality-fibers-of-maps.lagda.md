# Functoriality of fibers of maps

```agda
module foundation.functoriality-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Any [morphism of arrows](foundation.morphisms-arrows.md) `(i , j , H)` from `f` to `g`

```text
        i
    A -----> X
    |        |
  f |        | g
    v        v
    B -----> Y
        j
```

induces a morphism of arrows between the [fiber inclusions](foundation-core.fibers-of-maps.md) of `f` and `g`, i.e., a [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
  fiber f b -----> fiber g (j b)
      |                  |
      |                  |
      V                  V
      A ---------------> X.
```

This operation from morphisms of arrows from `f` to `g` to morphisms of arrows between their fiber inclusions is the **functorial action of fibers**. The functorial action obeys the functor laws, i.e., it preserves identity morphisms and composition.

## Definitions

### Any commuting square induces a family of maps between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) (b : B)
  where

  map-domain-hom-arrow-fiber :
    fiber f b → fiber g (map-codomain-hom-arrow f g α b)
  pr1 (map-domain-hom-arrow-fiber (y , p)) = map-domain-hom-arrow f g α y
  pr2 (map-domain-hom-arrow-fiber (y , p)) =
    inv (coh-hom-arrow f g α y) ∙ ap (map-codomain-hom-arrow f g α) p

  map-fiber :
    fiber f b → fiber g (map-codomain-hom-arrow f g α b)
  map-fiber = map-domain-hom-arrow-fiber

  map-codomain-hom-arrow-fiber : A → X
  map-codomain-hom-arrow-fiber = map-domain-hom-arrow f g α

  coh-hom-arrow-fiber :
    coherence-square-maps
      ( map-domain-hom-arrow-fiber)
      ( inclusion-fiber f)
      ( inclusion-fiber g)
      ( map-domain-hom-arrow f g α)
  coh-hom-arrow-fiber = refl-htpy

  hom-arrow-fiber :
    hom-arrow
      ( inclusion-fiber f {b})
      ( inclusion-fiber g {map-codomain-hom-arrow f g α b})
  pr1 hom-arrow-fiber = map-domain-hom-arrow-fiber
  pr1 (pr2 hom-arrow-fiber) = map-codomain-hom-arrow-fiber
  pr2 (pr2 hom-arrow-fiber) = coh-hom-arrow-fiber
```

### Any cone induces a family of maps between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (a : A)
  where

  map-fiber-cone : fiber (vertical-map-cone f g c) a → fiber g (f a)
  map-fiber-cone =
    map-domain-hom-arrow-fiber
      ( vertical-map-cone f g c)
      ( g)
      ( hom-arrow-cone f g c)
      ( a)
```

## Properties

### The functorial action of `fiber` preserves the identity function

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where
  
  preserves-id-map-fiber :
    map-domain-hom-arrow-fiber f f id-hom-arrow b ~ id
  preserves-id-map-fiber (a , refl) = refl

  coh-preserves-id-hom-arrow-fiber :
    coherence-square-homotopies
      ( refl-htpy)
      ( refl-htpy)
      ( coh-hom-arrow-fiber f f id-hom-arrow b)
      ( inclusion-fiber f ·l preserves-id-map-fiber)
  coh-preserves-id-hom-arrow-fiber (a , refl) = refl 

  preserves-id-hom-arrow-fiber :
    htpy-hom-arrow
      ( inclusion-fiber f)
      ( inclusion-fiber f)
      ( hom-arrow-fiber f f id-hom-arrow b)
      ( id-hom-arrow)
  pr1 preserves-id-hom-arrow-fiber = preserves-id-map-fiber
  pr1 (pr2 preserves-id-hom-arrow-fiber) = refl-htpy
  pr2 (pr2 preserves-id-hom-arrow-fiber) = coh-preserves-id-hom-arrow-fiber
```

### The functorial action of `fiber` preserves composition of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V) (β : hom-arrow g h) (α : hom-arrow f g)
  (b : B)
  where

  preserves-comp-map-fiber :
    map-fiber f h (comp-hom-arrow f g h β α) b ~
    map-fiber g h β (map-codomain-hom-arrow f g α b) ∘ map-fiber f g α b
  preserves-comp-map-fiber (a , refl) =
    ap
      ( pair _)
      ( ( right-unit) ∙
        ( distributive-inv-concat
          ( ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α a))
          ( coh-hom-arrow g h β (map-domain-hom-arrow f g α a))) ∙
        ( ap
          ( concat (inv (coh-hom-arrow g h β (pr1 α a))) _)
          ( inv
            ( ( ap (ap (map-codomain-hom-arrow g h β)) right-unit) ∙
              ( ap-inv
                ( map-codomain-hom-arrow g h β)
                ( coh-hom-arrow f g α a))))))

  compute-left-whisker-inclusion-fiber-preserves-comp-map-fiber :
    inclusion-fiber h ·l preserves-comp-map-fiber ~ refl-htpy
  compute-left-whisker-inclusion-fiber-preserves-comp-map-fiber (a , refl) =
    ( inv (ap-comp (inclusion-fiber h) (pair _) _)) ∙
    ( ap-const _ _)

  coh-preserves-comp-hom-arrow-fiber :
    coherence-square-homotopies
      ( refl-htpy)
      ( coh-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber h)
        ( hom-arrow-fiber f h (comp-hom-arrow f g h β α) b))
      ( coh-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber h)
        ( comp-hom-arrow
          ( inclusion-fiber f)
          ( inclusion-fiber g)
          ( inclusion-fiber h)
          ( hom-arrow-fiber g h β (map-codomain-hom-arrow f g α b))
          ( hom-arrow-fiber f g α b)))
      ( inclusion-fiber h ·l preserves-comp-map-fiber)
  coh-preserves-comp-hom-arrow-fiber p =
    ap
      ( concat _ _)
      ( compute-left-whisker-inclusion-fiber-preserves-comp-map-fiber p)
  
  preserves-comp-hom-arrow-fiber :
    htpy-hom-arrow
      ( inclusion-fiber f)
      ( inclusion-fiber h)
      ( hom-arrow-fiber f h (comp-hom-arrow f g h β α) b)
      ( comp-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber g)
        ( inclusion-fiber h)
        ( hom-arrow-fiber g h β (map-codomain-hom-arrow f g α b))
        ( hom-arrow-fiber f g α b))
  pr1 preserves-comp-hom-arrow-fiber = preserves-comp-map-fiber
  pr1 (pr2 preserves-comp-hom-arrow-fiber) = refl-htpy
  pr2 (pr2 preserves-comp-hom-arrow-fiber) = coh-preserves-comp-hom-arrow-fiber
```

### Computing `map-fiber-cone` of a horizontal pasting of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  map-fiber-pasting-horizontal-cone :
    (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) (x : X) →
    ( map-fiber-cone (j ∘ i) h (pasting-horizontal-cone i j h c d) x) ~
    ( map-fiber-cone j h c (i x) ∘
      map-fiber-cone i (vertical-map-cone j h c) d x)
  map-fiber-pasting-horizontal-cone
    (g , q , K) (f , p , H) .(f a) (a , refl) =
    eq-pair-eq-pr2
      ( ( ap
          ( concat' (h (q (p a))) refl)
          ( distributive-inv-concat (ap j (H a)) (K (p a)))) ∙
        ( assoc (inv (K (p a))) (inv (ap j (H a))) refl) ∙
        ( ap
          ( concat (inv (K (p a))) (j (i (f a))))
          ( ( ap (concat' (j (g (p a))) refl) (inv (ap-inv j (H a)))) ∙
            ( inv (ap-concat j (inv (H a)) refl)))))
```

### Computing `map-fiber-cone` of a horizontal pasting of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  map-fiber-pasting-vertical-cone :
    (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) (x : C) →
    ( ( map-fiber-cone f (g ∘ h) (pasting-vertical-cone f g h c d) x) ∘
      ( inv-map-compute-fiber-comp (pr1 c) (pr1 d) x)) ~
    ( ( inv-map-compute-fiber-comp g h (f x)) ∘
      ( map-Σ
        ( λ t → fiber h (pr1 t))
        ( map-fiber-cone f g c x)
        ( λ t → map-fiber-cone (pr1 (pr2 c)) h d (pr1 t))))
  map-fiber-pasting-vertical-cone
    (p , q , H) (p' , q' , H') .(p (p' a))
    ((.(p' a) , refl) , (a , refl)) =
    eq-pair-eq-pr2
      ( ( right-unit) ∙
        ( distributive-inv-concat (H (p' a)) (ap g (H' a))) ∙
        ( ap
          ( concat (inv (ap g (H' a))) (f (p (p' a))))
          ( inv right-unit)) ∙
        ( ap
          ( concat' (g (h (q' a)))
            ( pr2
              ( map-fiber-cone f g
                ( p , q , H)
                ( p (p' a))
                ( p' a , refl))))
          ( ( inv (ap-inv g (H' a))) ∙
            ( ap (ap g) (inv right-unit)))))
```

## See also

- In [retracts of maps](foundation.retracts-of-maps.md), we show that if `g` is
  a retract of `g'`, then the fibers of `g` are retracts of the fibers of `g'`.

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
