# The functoriality of `fib`

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

Any commuting square

induces a map between the fibers of the vertical maps

## Definitions

### Any cone induces a family of maps between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  map-fib-cone : (x : A) → fib (pr1 c) x → fib g (f x)
  pr1 (map-fib-cone x t) = pr1 (pr2 c) (pr1 t)
  pr2 (map-fib-cone x t) = (inv (pr2 (pr2 c) (pr1 t))) ∙ (ap f (pr2 t))

map-fib-cone-id :
  {l1 l2 : Level} {B : UU l1} {X : UU l2} (g : B → X) (x : X) →
  map-fib-cone id g (triple g id refl-htpy) x ~ id
map-fib-cone-id g .(g b) (pair b refl) =
  refl
```

## Properties

### Computing `map-fib-cone` of a horizontal pasting of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  map-fib-pasting-horizontal-cone :
    (c : cone j h B) (d : cone i (pr1 c) A) → (x : X) →
    ( map-fib-cone (j ∘ i) h (pasting-horizontal-cone i j h c d) x) ~
    ( (map-fib-cone j h c (i x)) ∘ (map-fib-cone i (pr1 c) d x))
  map-fib-pasting-horizontal-cone
    (pair g (pair q K)) (pair f (pair p H)) .(f a) (pair a refl) =
    eq-pair-Σ
      ( refl)
      ( ( ap
          ( concat' (h (q (p a))) refl)
          ( distributive-inv-concat (ap j (H a)) (K (p a)))) ∙
        ( ( assoc (inv (K (p a))) (inv (ap j (H a))) refl) ∙
          ( ap
            ( concat (inv (K (p a))) (j (i (f a))))
            ( ( ap (concat' (j (g (p a))) refl) (inv (ap-inv j (H a)))) ∙
              ( inv (ap-concat j (inv (H a)) refl))))))
```

### Computing `map-fib-cone` of a horizontal pasting of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  map-fib-pasting-vertical-cone :
    (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) (x : C) →
    ( ( map-fib-cone f (g ∘ h) (pasting-vertical-cone f g h c d) x) ∘
      ( inv-map-compute-fib-comp (pr1 c) (pr1 d) x)) ~
    ( ( inv-map-compute-fib-comp g h (f x)) ∘
      ( map-Σ
        ( λ t → fib h (pr1 t))
        ( map-fib-cone f g c x)
        ( λ t → map-fib-cone (pr1 (pr2 c)) h d (pr1 t))))
  map-fib-pasting-vertical-cone
    (pair p (pair q H)) (pair p' (pair q' H')) .(p (p' a))
    (pair (pair .(p' a) refl) (pair a refl)) =
    eq-pair-Σ refl
      ( ( right-unit) ∙
        ( ( distributive-inv-concat (H (p' a)) (ap g (H' a))) ∙
          ( ( ap
              ( concat (inv (ap g (H' a))) (f (p (p' a))))
              ( inv right-unit)) ∙
            ( ap
              ( concat' (g (h (q' a)))
                ( pr2
                  ( map-fib-cone f g
                    ( triple p q H)
                    ( p (p' a))
                    ( pair (p' a) refl))))
              ( ( inv (ap-inv g (H' a))) ∙
                ( ap (ap g) (inv right-unit)))))))
```

## See also

- Equality proofs in the fiber of a map are characterized in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).
