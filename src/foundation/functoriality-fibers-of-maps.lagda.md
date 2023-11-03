# Functoriality of fibers of maps

```agda
module foundation.functoriality-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Any [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
        f'
    S -----> B
    |        |
  g'|        | g
    v        v
    A -----> X
        f
```

induces a map between the [fibers](foundation-core.fibers-of-maps.md) of the
vertical maps

```text
  fiber g' x → fiber g (f x).
```

## Definitions

### Any cone induces a family of maps between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  map-fiber-cone : (x : A) → fiber (pr1 c) x → fiber g (f x)
  pr1 (map-fiber-cone x t) = pr1 (pr2 c) (pr1 t)
  pr2 (map-fiber-cone x t) = inv (pr2 (pr2 c) (pr1 t)) ∙ ap f (pr2 t)

map-fiber-cone-id :
  {l1 l2 : Level} {B : UU l1} {X : UU l2} (g : B → X) (x : X) →
  map-fiber-cone id g (g , id , refl-htpy) x ~ id
map-fiber-cone-id g .(g b) (b , refl) = refl
```

## Properties

### Computing `map-fiber-cone` of a horizontal pasting of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  map-fiber-pasting-horizontal-cone :
    (c : cone j h B) (d : cone i (pr1 c) A) → (x : X) →
    ( map-fiber-cone (j ∘ i) h (pasting-horizontal-cone i j h c d) x) ~
    ( map-fiber-cone j h c (i x) ∘ map-fiber-cone i (pr1 c) d x)
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

- In [retracts of maps](orthogonal-factorization-systems.retracts-of-maps.md),
  we show that if `g` is a retract of `g'`, then the fibers of `g` are retracts
  of the fibers of `g'`.

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
