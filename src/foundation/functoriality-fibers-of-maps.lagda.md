# Functoriality of fibers of maps

```agda
module foundation.functoriality-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.homotopies-morphisms-arrows
open import foundation.morphisms-arrows
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
[fiber inclusions](foundation-core.fibers-of-maps.md) of `f` and `g`, i.e., a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
  fiber f b -----> fiber g (j b)
      |                  |
      |                  |
      ∨                  ∨
      A ---------------> X.
```

This operation from morphisms of arrows from `f` to `g` to morphisms of arrows
between their fiber inclusions is the **functorial action of fibers**. The
functorial action obeys the functor laws, i.e., it preserves identity morphisms
and composition.

## Definitions

### Any commuting square induces a family of maps between the fibers of the vertical maps

Our definition of `map-domain-hom-arrow-fiber` is given in such a way that it
always computes nicely.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) (b : B)
  where

  map-domain-hom-arrow-fiber :
    fiber f b → fiber g (map-codomain-hom-arrow f g α b)
  map-domain-hom-arrow-fiber =
    map-Σ _
      ( map-domain-hom-arrow f g α)
      ( λ a p →
        inv (coh-hom-arrow f g α a) ∙ ap (map-codomain-hom-arrow f g α) p)

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

  map-fiber-vertical-map-cone :
    fiber (vertical-map-cone f g c) a → fiber g (f a)
  map-fiber-vertical-map-cone =
    map-domain-hom-arrow-fiber
      ( vertical-map-cone f g c)
      ( g)
      ( hom-arrow-cone f g c)
      ( a)
```

### Any cone induces a family of maps between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (b : B)
  where

  map-fiber-horizontal-map-cone :
    fiber (horizontal-map-cone f g c) b → fiber f (g b)
  map-fiber-horizontal-map-cone =
    map-domain-hom-arrow-fiber
      ( horizontal-map-cone f g c)
      ( f)
      ( hom-arrow-cone' f g c)
      ( b)
```

### For any `f : A → B` and any identification `p : b ＝ b'` in `B`, we obtain a morphism of arrows between the fiber inclusion at `b` to the fiber inclusion at `b'`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  tr-hom-arrow-inclusion-fiber :
    {b b' : B} (p : b ＝ b') →
    hom-arrow (inclusion-fiber f {b}) (inclusion-fiber f {b'})
  pr1 (tr-hom-arrow-inclusion-fiber p) = tot (λ a → concat' (f a) p)
  pr1 (pr2 (tr-hom-arrow-inclusion-fiber p)) = id
  pr2 (pr2 (tr-hom-arrow-inclusion-fiber p)) = refl-htpy
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
            ( ( ap² (map-codomain-hom-arrow g h β) right-unit) ∙
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

### The functorial action of `fiber` preserves homotopies of morphisms of fibers

Given two morphisms of arrows

```text
        α₀
      ------>
    A ------> X
    |   β₀    |
    |         |
  f |  α  β   | g
    |         |
    ∨   α₁    ∨
    B ------> Y
      ------>
        β₁
```

with a homotopy `γ : α ~ β` of morphisms of arrows, we obtain a commuting
diagram of the form

```text
           fiber g (α₁ b)
            ∧     |   \
           /      |    \ (x , q) ↦ (x , q ∙ γ₁ b)
          /       |     \
         /        |      ∨
  fiber f b --------> fiber g (β₁ b)
        |         |     /
        |         |    /
        |         |   /
        |         |  /
        ∨         ∨ ∨
        A -------> X
```

To show that we have such a commuting diagram, we have to show that the top
triangle commutes, and that there is a homotopy filling the diagram:

We first show that the top triangle commutes. To see this, let
`(a , refl) : fiber f (f a)`. Then we have to show that

```text
  ((x , q) ↦ (x , q ∙ γ₁ b)) (map-fiber f g α (a , refl)) ＝
  map-fiber f g β (a , refl)
```

Simply computing the left-hand side and the right-hand side, we're tasked with
constructing an identification

```text
  (α₀ a , ((α a)⁻¹ ∙ refl) ∙ γ₁ (f a)) ＝ (β₀ a , (β a)⁻¹ ∙ refl)
```

By the characterization of equality in fibers, it suffices to construct
identifications

```text
  p : α₀ a ＝ β₀ a
  q : ap g p ∙ ((β a)⁻¹ ∙ refl) ＝ ((α a)⁻¹ ∙ refl) ∙ γ₁ (f a)
```

The first identification is `γ₀ a`. To obtain the second identification, we
first simplify using the right unit law. I.e., it suffices to construct an
identification

```text
  ap g p ∙ (β a)⁻¹ ＝ (α a)⁻¹ ∙ γ₁ (f a).
```

Now we proceed by transposing equality on both sides, i.e., it suffices to
construct an identification

```text
  α a ∙ ap g p ＝ γ₁ (f a) ∙ β a.
```

The identification `γ a` has exactly this type. This completes the construction
of the homotopy witnessing that the upper triangle commutes. Since it is
constructed as a family of identifications of the form

```text
  eq-Eq-fiber g (γ₀ a) _,
```

it follows that when we left whisker this homotopy with `inclusion-fiber g`, we
recover the homotopy `γ₀ ·r inclusion-fiber f`.

Now it remains to fill a coherence for the square of homotopies

```text
                   γ₀ ·r i
                · ---------> ·
                |            |
 coh (tr ∘ α b) |            | coh-hom-arrow-fiber f g β b
    ≐ refl-htpy |            | ≐ refl-htpy
                ∨            ∨
                · ---------> ·
                   i ·r H
```

where `H` is the homotopy that we just constructed, witnessing that the upper
triangle commutes, and where we have written `i` for all fiber inclusions.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α β : hom-arrow f g) (γ : htpy-hom-arrow f g α β)
  (b : B)
  where

  htpy-fiber :
    ( tot (λ x → concat' (g x) (htpy-codomain-htpy-hom-arrow f g α β γ b)) ∘
      map-fiber f g α b) ~
    ( map-fiber f g β b)
  htpy-fiber (a , refl) =
    eq-Eq-fiber g
      ( map-codomain-hom-arrow f g β (f a))
      ( htpy-domain-htpy-hom-arrow f g α β γ a)
      ( ( ap
          ( concat
            ( ap g (htpy-domain-htpy-hom-arrow f g α β γ a))
            ( map-codomain-hom-arrow f g β (f a)))
          ( right-unit)) ∙
        ( double-transpose-eq-concat'
          ( htpy-codomain-htpy-hom-arrow f g α β γ (f a))
          ( coh-hom-arrow f g α a)
          ( coh-hom-arrow f g β a)
          ( ap g (htpy-domain-htpy-hom-arrow f g α β γ a))
          ( coh-htpy-hom-arrow f g α β γ a)) ∙
        ( inv
          ( ap
            ( concat'
              ( g (map-domain-hom-arrow f g α a))
              ( htpy-codomain-htpy-hom-arrow f g α β γ (f a)))
            ( right-unit))))

  compute-left-whisker-inclusion-fiber-htpy-fiber :
    inclusion-fiber g ·l htpy-fiber ~
    htpy-domain-htpy-hom-arrow f g α β γ ·r inclusion-fiber f
  compute-left-whisker-inclusion-fiber-htpy-fiber (a , refl) =
    compute-ap-inclusion-fiber-eq-Eq-fiber g
      ( map-codomain-hom-arrow f g β (f a))
      ( htpy-domain-htpy-hom-arrow f g α β γ a)
      ( _)

  htpy-codomain-htpy-hom-arrow-fiber :
    map-codomain-hom-arrow-fiber f g α b ~
    map-codomain-hom-arrow-fiber f g β b
  htpy-codomain-htpy-hom-arrow-fiber =
    htpy-domain-htpy-hom-arrow f g α β γ

  coh-htpy-hom-arrow-fiber :
    coherence-square-homotopies
      ( htpy-domain-htpy-hom-arrow f g α β γ ·r inclusion-fiber f)
      ( refl-htpy)
      ( refl-htpy)
      ( inclusion-fiber g ·l htpy-fiber)
  coh-htpy-hom-arrow-fiber =
    compute-left-whisker-inclusion-fiber-htpy-fiber ∙h inv-htpy right-unit-htpy

  htpy-hom-arrow-fiber :
    htpy-hom-arrow
      ( inclusion-fiber f)
      ( inclusion-fiber g)
      ( comp-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber g)
        ( inclusion-fiber g)
        ( tr-hom-arrow-inclusion-fiber g
          ( htpy-codomain-htpy-hom-arrow f g α β γ b))
        ( hom-arrow-fiber f g α b))
      ( hom-arrow-fiber f g β b)
  pr1 htpy-hom-arrow-fiber = htpy-fiber
  pr1 (pr2 htpy-hom-arrow-fiber) = htpy-codomain-htpy-hom-arrow-fiber
  pr2 (pr2 htpy-hom-arrow-fiber) = coh-htpy-hom-arrow-fiber
```

### Computing `map-fiber-vertical-map-cone` of a horizontal pasting of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  preserves-pasting-horizontal-map-fiber-vertical-map-cone :
    (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) (x : X) →
    ( map-fiber-vertical-map-cone (j ∘ i) h
      ( pasting-horizontal-cone i j h c d)
      ( x)) ~
    ( map-fiber-vertical-map-cone j h c (i x) ∘
      map-fiber-vertical-map-cone i (vertical-map-cone j h c) d x)
  preserves-pasting-horizontal-map-fiber-vertical-map-cone c d =
    preserves-comp-map-fiber
      ( vertical-map-cone i (vertical-map-cone j h c) d)
      ( vertical-map-cone j h c)
      ( h)
      ( hom-arrow-cone j h c)
      ( hom-arrow-cone i (vertical-map-cone j h c) d)
```

### Computing `map-fiber-vertical-map-cone` of a horizontal pasting of cones

Note: There should be a definition of vertical composition of morphisms of
arrows, and a proof that `hom-arrow-fiber` preserves vertical composition.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  preserves-pasting-vertical-map-fiber-vertical-map-cone :
    (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) (x : C) →
    ( ( map-fiber-vertical-map-cone f (g ∘ h)
        ( pasting-vertical-cone f g h c d)
        ( x)) ∘
      ( map-inv-compute-fiber-comp (pr1 c) (pr1 d) x)) ~
    ( ( map-inv-compute-fiber-comp g h (f x)) ∘
      ( map-Σ
        ( λ t → fiber h (pr1 t))
        ( map-fiber-vertical-map-cone f g c x)
        ( λ t →
          map-fiber-vertical-map-cone (horizontal-map-cone f g c) h d (pr1 t))))
  preserves-pasting-vertical-map-fiber-vertical-map-cone
    (p , q , H) (p' , q' , H') .(p (p' a))
    ((.(p' a) , refl) , (a , refl)) =
    eq-pair-eq-fiber
      ( ( right-unit) ∙
        ( distributive-inv-concat (H (p' a)) (ap g (H' a))) ∙
        ( ap
          ( concat (inv (ap g (H' a))) (f (p (p' a))))
          ( inv right-unit)) ∙
        ( ap
          ( concat' (g (h (q' a)))
            ( pr2
              ( map-fiber-vertical-map-cone f g
                ( p , q , H)
                ( p (p' a))
                ( p' a , refl))))
          ( ( inv (ap-inv g (H' a))) ∙
            ( ap² g (inv right-unit)))))
```

## See also

- In [retracts of maps](foundation.retracts-of-maps.md), we show that if `g` is
  a retract of `g'`, then the fibers of `g` are retracts of the fibers of `g'`.

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
