---
title: Pullbacks
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.pullbacks where

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares
open import foundation-core.cones-pullbacks
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equality-cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.morphisms-cospans
open import foundation-core.universal-property-pullbacks
open import foundation-core.universe-levels

open import foundation.diagonal-maps-of-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
```

## Definitions

### The canonical pullback of a cospan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  canonical-pullback : UU ((l1 ⊔ l2) ⊔ l3)
  canonical-pullback = Σ A (λ x → Σ B (λ y → f x ＝ g y))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X} {g : B → X}
  where
   
  π₁ : canonical-pullback f g → A
  π₁ = pr1

  π₂ : canonical-pullback f g → B
  π₂ t = pr1 (pr2 t)

  π₃ : (f ∘ π₁) ~ (g ∘ π₂)
  π₃ t = pr2 (pr2 t)
```

### The cone at the canonical pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where
  
  cone-canonical-pullback : cone f g (canonical-pullback f g)
  pr1 cone-canonical-pullback = π₁
  pr1 (pr2 cone-canonical-pullback) = π₂
  pr2 (pr2 cone-canonical-pullback) = π₃
```

### The gap-map into the canonical pullback

The gap map of a square is the map fron the vertex of the cone into the canonical pullback.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) 
  where

  gap : cone f g C → C → canonical-pullback f g
  pr1 (gap t z) = pr1 t z
  pr1 (pr2 (gap t z)) = pr1 (pr2 t) z
  pr2 (pr2 (gap t z)) = pr2 (pr2 t) z
```

### The `is-pullback` property

The proposition is-pullback is the assertion that the gap map is an equivalence. Note that this proposition is small, whereas the universal property is a large proposition.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) 
  where

  is-pullback : cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback c = is-equiv (gap f g c)
```

### Functoriality of canonical pullbacks

```agda
functor-canonical-pullback :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  hom-cospan f' g' f g →
  canonical-pullback f' g' → canonical-pullback f g
functor-canonical-pullback f g f' g'
  (pair hA (pair hB (pair hX (pair HA HB)))) (pair a' (pair b' p')) =
  triple (hA a') (hB b') ((HA a') ∙ ((ap hX p') ∙ (inv (HB b'))))
```

## Properties

### Characterization of the identity type of the canonical pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  Eq-canonical-pullback : (t t' : canonical-pullback f g) → UU (l1 ⊔ (l2 ⊔ l3))
  Eq-canonical-pullback (pair a bp) t' =
    let b = pr1 bp
        p = pr2 bp
        a' = pr1 t'
        b' = pr1 (pr2 t')
        p' = pr2 (pr2 t')
    in
    Σ (a ＝ a') (λ α → Σ (b ＝ b') (λ β → ((ap f α) ∙ p') ＝ (p ∙ (ap g β))))

  refl-Eq-canonical-pullback :
    (t : canonical-pullback f g) → Eq-canonical-pullback t t
  pr1 (refl-Eq-canonical-pullback (pair a (pair b p))) = refl
  pr1 (pr2 (refl-Eq-canonical-pullback (pair a (pair b p)))) = refl
  pr2 (pr2 (refl-Eq-canonical-pullback (pair a (pair b p)))) = inv right-unit

  Eq-eq-canonical-pullback :
    (s t : canonical-pullback f g) → s ＝ t → Eq-canonical-pullback s t
  Eq-eq-canonical-pullback s .s refl = refl-Eq-canonical-pullback s

  extensionality-canonical-pullback :
    (t t' : canonical-pullback f g) → (t ＝ t') ≃ Eq-canonical-pullback t t'
  extensionality-canonical-pullback (pair a (pair b p)) =
    extensionality-Σ
      ( λ {a'} bp' α →
        Σ (b ＝ pr1 bp') (λ β → (ap f α ∙ pr2 bp') ＝ (p ∙ ap g β)))
      ( refl)
      ( pair refl (inv right-unit))
      ( λ x → id-equiv)
      ( extensionality-Σ
        ( λ {b'} p' β → p' ＝ (p ∙ ap g β))
        ( refl)
        ( inv right-unit)
        ( λ y → id-equiv)
        ( λ p' → equiv-concat' p' (inv right-unit) ∘e equiv-inv p p'))

  map-extensionality-canonical-pullback :
    { s t : canonical-pullback f g} →
    ( α : pr1 s ＝ pr1 t) (β : pr1 (pr2 s) ＝ pr1 (pr2 t)) →
    ( ((ap f α) ∙ (pr2 (pr2 t))) ＝ ((pr2 (pr2 s)) ∙ (ap g β))) → s ＝ t
  map-extensionality-canonical-pullback {s} {t} α β γ =
    map-inv-equiv
      ( extensionality-canonical-pullback s t)
      ( triple α β γ)
```

### The canonical pullback satisfies the universal property of pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  abstract
    universal-property-pullback-canonical-pullback : 
      {l : Level} →
      universal-property-pullback l f g (cone-canonical-pullback f g)
    universal-property-pullback-canonical-pullback C =
      is-equiv-comp
        ( cone-map f g (cone-canonical-pullback f g))
        ( tot (λ p → map-distributive-Π-Σ))
        ( mapping-into-Σ)
        ( refl-htpy)
        ( is-equiv-mapping-into-Σ)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ p → is-equiv-map-distributive-Π-Σ))
```

### A cone is equal to the value of cone-map at its own gap map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) 
  where

  htpy-cone-up-pullback-canonical-pullback :
    (c : cone f g C) →
    htpy-cone f g (cone-map f g (cone-canonical-pullback f g) (gap f g c)) c
  pr1 (htpy-cone-up-pullback-canonical-pullback c) = refl-htpy
  pr1 (pr2 (htpy-cone-up-pullback-canonical-pullback c)) = refl-htpy
  pr2 (pr2 (htpy-cone-up-pullback-canonical-pullback c)) = right-unit-htpy
```

### A cone satisfies the universal property of the pullback if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) 
  where

  abstract
    is-pullback-universal-property-pullback :
      (c : cone f g C) →
      ({l : Level} → universal-property-pullback l f g c) → is-pullback f g c
    is-pullback-universal-property-pullback c up =
      is-equiv-up-pullback-up-pullback
        ( cone-canonical-pullback f g)
        ( c)
        ( gap f g c)
        ( htpy-cone-up-pullback-canonical-pullback f g c)
        ( universal-property-pullback-canonical-pullback f g)
        ( up)

  abstract
    universal-property-pullback-is-pullback :
      (c : cone f g C) → is-pullback f g c →
      {l : Level} → universal-property-pullback l f g c
    universal-property-pullback-is-pullback c is-pullback-c =
      up-pullback-up-pullback-is-equiv
        ( cone-canonical-pullback f g)
        ( c)
        ( gap f g c)
        ( htpy-cone-up-pullback-canonical-pullback f g c)
        ( is-pullback-c)
        ( universal-property-pullback-canonical-pullback f g)
```

### The pullback of a type family

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  where

  canonical-pullback-Σ : UU (l1 ⊔ l3)
  canonical-pullback-Σ = Σ A (λ x → Q (f x))
  
  cone-subst : cone f (pr1 {B = Q}) canonical-pullback-Σ
  pr1 cone-subst = pr1
  pr1 (pr2 cone-subst) = map-Σ-map-base f Q
  pr2 (pr2 cone-subst) = refl-htpy

  inv-gap-cone-subst : canonical-pullback f (pr1 {B = Q}) → canonical-pullback-Σ
  pr1 (inv-gap-cone-subst (pair x (pair (pair .(f x) q) refl))) = x
  pr2 (inv-gap-cone-subst (pair x (pair (pair .(f x) q) refl))) = q
  
  abstract
    issec-inv-gap-cone-subst :
      ((gap f (pr1 {B = Q}) cone-subst) ∘ inv-gap-cone-subst) ~ id
    issec-inv-gap-cone-subst (pair x (pair (pair .(f x) q) refl)) = refl

  abstract
    isretr-inv-gap-cone-subst :
      (inv-gap-cone-subst ∘ (gap f (pr1 {B = Q}) cone-subst)) ~ id
    isretr-inv-gap-cone-subst (pair x q) = refl

  abstract
    is-pullback-cone-subst : is-pullback f (pr1 {B = Q}) cone-subst
    is-pullback-cone-subst =
      is-equiv-has-inverse
        inv-gap-cone-subst
        issec-inv-gap-cone-subst
        isretr-inv-gap-cone-subst
```

### A family of maps over a base map induces a pullback square if and only if it is a family of equivalences.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
  (Q : B → UU l4) (f : A → B) (g : (x : A) → (P x) → (Q (f x)))
  where
  
  cone-map-Σ : cone f (pr1 {B = Q}) (Σ A P)
  pr1 cone-map-Σ = pr1
  pr1 (pr2 cone-map-Σ) = map-Σ Q f g
  pr2 (pr2 cone-map-Σ) = refl-htpy

  abstract
    is-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → is-pullback f (pr1 {B = Q}) cone-map-Σ
    is-pullback-is-fiberwise-equiv is-equiv-g =
      is-equiv-comp
        ( gap f pr1 cone-map-Σ)
        ( gap f pr1 (cone-subst f Q))
        ( tot g)
        ( refl-htpy)
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-g)
        ( is-pullback-cone-subst f Q)

  abstract
    universal-property-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → {l : Level} →
      universal-property-pullback l f (pr1 {B = Q}) cone-map-Σ
    universal-property-pullback-is-fiberwise-equiv is-equiv-g =
      universal-property-pullback-is-pullback f pr1 cone-map-Σ
        ( is-pullback-is-fiberwise-equiv is-equiv-g)

  abstract
    is-fiberwise-equiv-is-pullback :
      is-pullback f (pr1 {B = Q}) cone-map-Σ → is-fiberwise-equiv g
    is-fiberwise-equiv-is-pullback is-pullback-cone-map-Σ =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-right-factor
          ( gap f pr1 cone-map-Σ)
          ( gap f pr1 (cone-subst f Q))
          ( tot g)
          ( refl-htpy)
          ( is-pullback-cone-subst f Q)
          ( is-pullback-cone-map-Σ))

  abstract
    is-fiberwise-equiv-universal-property-pullback :
      ( {l : Level} →
        universal-property-pullback l f (pr1 {B = Q}) cone-map-Σ) →
      is-fiberwise-equiv g
    is-fiberwise-equiv-universal-property-pullback up =
      is-fiberwise-equiv-is-pullback
        ( is-pullback-universal-property-pullback f pr1 cone-map-Σ up)
```

### A cone is a pullback if and only if it induces a family of equivalences between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  square-tot-fib-square :
    ( (gap f g c) ∘ (map-equiv-total-fib (pr1 c))) ~
    ( (tot (λ a → tot (λ b → inv))) ∘ (tot (fib-square f g c)))
  square-tot-fib-square (pair .((pr1 c) x) (pair x refl)) =
    eq-pair-Σ refl
      ( eq-pair-Σ refl
        ( inv ((ap inv right-unit) ∙ (inv-inv (pr2 (pr2 c) x)))))

  abstract
    is-fiberwise-equiv-fib-square-is-pullback :
      is-pullback f g c → is-fiberwise-equiv (fib-square f g c)
    is-fiberwise-equiv-fib-square-is-pullback pb =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fib (pr1 c))
          ( tot (λ x → tot (λ y → inv)))
          ( tot (fib-square f g c))
          ( gap f g c)
          ( square-tot-fib-square)
          ( is-equiv-map-equiv-total-fib (pr1 c))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ x → is-equiv-tot-is-fiberwise-equiv
              ( λ y → is-equiv-inv (g y) (f x))))
          ( pb))

  abstract
    is-pullback-is-fiberwise-equiv-fib-square :
      is-fiberwise-equiv (fib-square f g c) → is-pullback f g c
    is-pullback-is-fiberwise-equiv-fib-square is-equiv-fsq =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fib (pr1 c))
        ( tot (λ x → tot (λ y → inv)))
        ( tot (fib-square f g c))
        ( gap f g c)
        ( square-tot-fib-square)
        ( is-equiv-map-equiv-total-fib (pr1 c))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ x → is-equiv-tot-is-fiberwise-equiv
            ( λ y → is-equiv-inv (g y) (f x))))
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-fsq)
```

### The horizontal pullback pasting property

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where
  
  cone-comp-horizontal :
    (c : cone j h B) → (cone i (pr1 c) A) → cone (j ∘ i) h A
  pr1 (cone-comp-horizontal (pair g (pair q K)) (pair f (pair p H))) = f
  pr1
    ( pr2
      ( cone-comp-horizontal (pair g (pair q K)) (pair f (pair p H)))) = q ∘ p
  pr2
    ( pr2
      ( cone-comp-horizontal (pair g (pair q K)) (pair f (pair p H)))) =
    coherence-square-comp-horizontal p q f g h i j H K

  fib-square-comp-horizontal :
    (c : cone j h B) (d : cone i (pr1 c) A) → (x : X) →
    ( fib-square (j ∘ i) h (cone-comp-horizontal c d) x) ~
    ( (fib-square j h c (i x)) ∘ (fib-square i (pr1 c) d x))
  fib-square-comp-horizontal
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

  abstract
    is-pullback-rectangle-is-pullback-left-square :
      (c : cone j h B) (d : cone i (pr1 c) A) →
      is-pullback j h c → is-pullback i (pr1 c) d →
      is-pullback (j ∘ i) h (cone-comp-horizontal c d)
    is-pullback-rectangle-is-pullback-left-square c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-fib-square (j ∘ i) h
        ( cone-comp-horizontal c d)
        ( λ x → is-equiv-comp
          ( fib-square (j ∘ i) h (cone-comp-horizontal c d) x)
          ( fib-square j h c (i x))
          ( fib-square i (pr1 c) d x)
          ( fib-square-comp-horizontal c d x)
          ( is-fiberwise-equiv-fib-square-is-pullback i (pr1 c) d is-pb-d x)
          ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x)))

  abstract
    is-pullback-left-square-is-pullback-rectangle :
      (c : cone j h B) (d : cone i (pr1 c) A) →
      is-pullback j h c → is-pullback (j ∘ i) h (cone-comp-horizontal c d) →
      is-pullback i (pr1 c) d
    is-pullback-left-square-is-pullback-rectangle c d is-pb-c is-pb-rect =
      is-pullback-is-fiberwise-equiv-fib-square i (pr1 c) d
        ( λ x → is-equiv-right-factor
          ( fib-square (j ∘ i) h (cone-comp-horizontal c d) x)
          ( fib-square j h c (i x))
          ( fib-square i (pr1 c) d x)
          ( fib-square-comp-horizontal c d x)
          ( is-fiberwise-equiv-fib-square-is-pullback j h c is-pb-c (i x))
          ( is-fiberwise-equiv-fib-square-is-pullback (j ∘ i) h
            ( cone-comp-horizontal c d) is-pb-rect x))
```

### The vertical pullback pasting property

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where
  
  cone-comp-vertical :
    (c : cone f g B) → cone (pr1 (pr2 c)) h A → cone f (g ∘ h) A
  pr1 (cone-comp-vertical (pair p (pair q H)) (pair p' (pair q' H'))) = p ∘ p'
  pr1 (pr2 (cone-comp-vertical (pair p (pair q H)) (pair p' (pair q' H')))) = q'
  pr2 (pr2 (cone-comp-vertical (pair p (pair q H)) (pair p' (pair q' H')))) =
    coherence-square-comp-vertical q' p' h q p g f H' H

  fib-square-comp-vertical : 
    (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) (x : C) →
    ( ( fib-square f (g ∘ h) (cone-comp-vertical c d) x) ∘
      ( inv-map-fib-comp (pr1 c) (pr1 d) x)) ~
    ( ( inv-map-fib-comp g h (f x)) ∘
      ( map-Σ
        ( λ t → fib h (pr1 t))
        ( fib-square f g c x)
        ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))))
  fib-square-comp-vertical
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
                  ( fib-square f g
                    ( triple p q H)
                    ( p (p' a))
                    ( pair (p' a) refl))))
              ( ( inv (ap-inv g (H' a))) ∙
                ( ap (ap g) (inv right-unit)))))))

  abstract
    is-pullback-top-is-pullback-rectangle :
      (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) →
      is-pullback f g c →
      is-pullback f (g ∘ h) (cone-comp-vertical c d) →
      is-pullback (pr1 (pr2 c)) h d
    is-pullback-top-is-pullback-rectangle c d is-pb-c is-pb-dc =
      is-pullback-is-fiberwise-equiv-fib-square (pr1 (pr2 c)) h d
        ( λ x → is-fiberwise-equiv-is-equiv-map-Σ
          ( λ t → fib h (pr1 t))
          ( fib-square f g c ((pr1 c) x))
          ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))
          ( is-fiberwise-equiv-fib-square-is-pullback f g c is-pb-c ((pr1 c) x))
          ( is-equiv-top-is-equiv-bottom-square
            ( inv-map-fib-comp (pr1 c) (pr1 d) ((pr1 c) x))
            ( inv-map-fib-comp g h (f ((pr1 c) x)))
            ( map-Σ
              ( λ t → fib h (pr1 t))
              ( fib-square f g c ((pr1 c) x))
              ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t)))
            ( fib-square f (g ∘ h) (cone-comp-vertical c d) ((pr1 c) x))
            ( fib-square-comp-vertical c d ((pr1 c) x))
            ( is-equiv-inv-map-fib-comp (pr1 c) (pr1 d) ((pr1 c) x))
            ( is-equiv-inv-map-fib-comp g h (f ((pr1 c) x)))
            ( is-fiberwise-equiv-fib-square-is-pullback f (g ∘ h)
              ( cone-comp-vertical c d) is-pb-dc ((pr1 c) x)))
          ( pair x refl))

  abstract
    is-pullback-rectangle-is-pullback-top :
      (c : cone f g B) (d : cone (pr1 (pr2 c)) h A) →
      is-pullback f g c →
      is-pullback (pr1 (pr2 c)) h d →
      is-pullback f (g ∘ h) (cone-comp-vertical c d)
    is-pullback-rectangle-is-pullback-top c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-fib-square f (g ∘ h)
        ( cone-comp-vertical c d)
        ( λ x → is-equiv-bottom-is-equiv-top-square
          ( inv-map-fib-comp (pr1 c) (pr1 d) x)
          ( inv-map-fib-comp g h (f x))
          ( map-Σ
            ( λ t → fib h (pr1 t))
            ( fib-square f g c x)
            ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t)))
          ( fib-square f (g ∘ h) (cone-comp-vertical c d) x)
          ( fib-square-comp-vertical c d x)
          ( is-equiv-inv-map-fib-comp (pr1 c) (pr1 d) x)
          ( is-equiv-inv-map-fib-comp g h (f x))
          ( is-equiv-map-Σ
            ( λ t → fib h (pr1 t))
            ( fib-square f g c x)
            ( λ t → fib-square (pr1 (pr2 c)) h d (pr1 t))
            ( is-fiberwise-equiv-fib-square-is-pullback f g c is-pb-c x)
            ( λ t → is-fiberwise-equiv-fib-square-is-pullback
              (pr1 (pr2 c)) h d is-pb-d (pr1 t)))) 
```

### Pullbacks are symmetric

```agda
map-canonical-pullback-swap :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → canonical-pullback f g → canonical-pullback g f
map-canonical-pullback-swap f g (pair a (pair b p)) =
  triple b a (inv p)

inv-inv-map-canonical-pullback-swap :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  (map-canonical-pullback-swap f g ∘ map-canonical-pullback-swap g f) ~ id
inv-inv-map-canonical-pullback-swap f g (pair b (pair a q)) =
  eq-pair-Σ refl (eq-pair-Σ refl (inv-inv q))

abstract
  is-equiv-map-canonical-pullback-swap :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-canonical-pullback-swap f g)
  is-equiv-map-canonical-pullback-swap f g =
    is-equiv-has-inverse
      ( map-canonical-pullback-swap g f)
      ( inv-inv-map-canonical-pullback-swap f g)
      ( inv-inv-map-canonical-pullback-swap g f)

triangle-map-canonical-pullback-swap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap g f (cone-swap f g c)) ~
  ( ( map-canonical-pullback-swap f g) ∘ ( gap f g c))
triangle-map-canonical-pullback-swap f g (pair p (pair q H)) x = refl

abstract
  is-pullback-cone-swap :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-pullback g f (cone-swap f g c)
  is-pullback-cone-swap f g c is-pb-c =
    is-equiv-comp
      ( gap g f (cone-swap f g c))
      ( map-canonical-pullback-swap f g)
      ( gap f g c)
      ( triangle-map-canonical-pullback-swap f g c)
      ( is-pb-c)
      ( is-equiv-map-canonical-pullback-swap f g)

abstract
  is-pullback-cone-swap' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback g f (cone-swap f g c) → is-pullback f g c
  is-pullback-cone-swap' f g c is-pb-c' =
    is-equiv-right-factor
      ( gap g f (cone-swap f g c))
      ( map-canonical-pullback-swap f g)
      ( gap f g c)
      ( triangle-map-canonical-pullback-swap f g c)
      ( is-equiv-map-canonical-pullback-swap f g)
      ( is-pb-c')
```

### Exponents of pullbacks are pullbacks

```agda
cone-exponent :
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} (T : UU l5)
  (f : A → X) (g : B → X) (c : cone f g C) →
  cone (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) (T → C)
cone-exponent T f g (pair p (pair q H)) =
  triple
    ( λ h → p ∘ h)
    ( λ h → q ∘ h)
    ( λ h → eq-htpy (H ·r h))

map-canonical-pullback-exponent :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4) →
  canonical-pullback (λ (h : T → A) → f ∘ h) (λ (h : T → B) → g ∘ h) →
  cone f g T
map-canonical-pullback-exponent f g T =
  tot (λ p → tot (λ q → htpy-eq))

abstract
  is-equiv-map-canonical-pullback-exponent :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
    (T : UU l4) → is-equiv (map-canonical-pullback-exponent f g T)
  is-equiv-map-canonical-pullback-exponent f g T =
    is-equiv-tot-is-fiberwise-equiv
      ( λ p → is-equiv-tot-is-fiberwise-equiv
        ( λ q → funext (f ∘ p) (g ∘ q)))

triangle-map-canonical-pullback-exponent :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  ( cone-map f g {C' = T} c) ~
  ( ( map-canonical-pullback-exponent f g T) ∘
    ( gap
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)))
triangle-map-canonical-pullback-exponent
  {A = A} {B} T f g (pair p (pair q H)) h =
  eq-pair-Σ refl (eq-pair-Σ refl (inv (issec-eq-htpy (H ·r h))))

abstract
  is-pullback-exponent-is-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
    (T : UU l5) →
    is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)
  is-pullback-exponent-is-pullback f g c is-pb-c T =
    is-equiv-right-factor
      ( cone-map f g c)
      ( map-canonical-pullback-exponent f g T)
      ( gap (_∘_ f) (_∘_ g) (cone-exponent T f g c))
      ( triangle-map-canonical-pullback-exponent T f g c)
      ( is-equiv-map-canonical-pullback-exponent f g T)
      ( universal-property-pullback-is-pullback f g c is-pb-c T)

abstract
  is-pullback-is-pullback-exponent :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ((l5 : Level) (T : UU l5) → is-pullback
      ( λ (h : T → A) → f ∘ h)
      ( λ (h : T → B) → g ∘ h)
      ( cone-exponent T f g c)) →
    is-pullback f g c
  is-pullback-is-pullback-exponent f g c is-pb-exp =
    is-pullback-universal-property-pullback f g c
      ( λ T → is-equiv-comp
        ( cone-map f g c)
        ( map-canonical-pullback-exponent f g T)
        ( gap (_∘_ f) (_∘_ g) (cone-exponent T f g c))
        ( triangle-map-canonical-pullback-exponent T f g c)
        ( is-pb-exp _ T)
        ( is-equiv-map-canonical-pullback-exponent f g T))
```

### Pullbacks can be "folded"

```agda
cone-fold :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) →
  cone f g C → cone (map-prod f g) (diagonal X) C
cone-fold f g (pair p (pair q H)) =
  triple (λ z → pair (p z) (q z)) (g ∘ q) (λ z → eq-pair (H z) refl)

map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  (f : A → X) → (g : B → X) →
  canonical-pullback f g → canonical-pullback (map-prod f g) (diagonal X)
map-cone-fold f g (pair a (pair b p)) =
  triple (pair a b) (g b) (eq-pair p refl)

inv-map-cone-fold :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} 
  (f : A → X) → (g : B → X) →
  canonical-pullback (map-prod f g) (diagonal X) → canonical-pullback f g
inv-map-cone-fold f g (pair (pair a b) (pair x α)) =
  triple a b ((ap pr1 α) ∙ (inv (ap pr2 α)))

abstract
  issec-inv-map-cone-fold :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    ((map-cone-fold f g) ∘ (inv-map-cone-fold f g)) ~ id
  issec-inv-map-cone-fold {A = A} {B} {X} f g (pair (pair a b) (pair x α)) =
    map-extensionality-canonical-pullback
      ( map-prod f g)
      ( diagonal X)
      refl
      ( ap pr2 α)
      ( ( ( ( inv (issec-pair-eq α)) ∙
            ( ap
              ( λ t → (eq-pair t (ap pr2 α)))
              ( ( ( inv right-unit) ∙
                  ( inv (ap (concat (ap pr1 α) x) (left-inv (ap pr2 α))))) ∙
                ( inv (assoc (ap pr1 α) (inv (ap pr2 α)) (ap pr2 α)))))) ∙
          ( eq-pair-concat
            ( (ap pr1 α) ∙ (inv (ap pr2 α)))
            ( ap pr2 α)
            ( refl)
            ( ap pr2 α))) ∙
        ( ap
          ( concat
            ( eq-pair ((ap pr1 α) ∙ (inv (ap pr2 α))) refl)
            ( pair x x))
          ( inv (ap-diagonal (ap pr2 α)))))

abstract
  isretr-inv-map-cone-fold :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) →
    ((inv-map-cone-fold f g) ∘ (map-cone-fold f g)) ~ id
  isretr-inv-map-cone-fold { A = A} { B = B} { X = X} f g (pair a (pair b p)) =
    map-extensionality-canonical-pullback {A = A} {B = B} {X = X} f g
      refl
      refl
      ( inv
        ( ( ap
            ( concat' (f a) refl)
            ( ( ( ap
                  ( λ t → t ∙
                    ( inv
                      ( ap pr2 (eq-pair
                      { s = pair (f a) (g b)}
                      { pair (g b) (g b)}
                      p refl))))
                    ( ap-pr1-eq-pair p refl)) ∙
                ( ap (λ t → p ∙ (inv t)) (ap-pr2-eq-pair p refl))) ∙
              ( right-unit))) ∙
          ( right-unit)))
  
abstract
  is-equiv-map-cone-fold :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-cone-fold f g)
  is-equiv-map-cone-fold f g =
    is-equiv-has-inverse
      ( inv-map-cone-fold f g)
      ( issec-inv-map-cone-fold f g)
      ( isretr-inv-map-cone-fold f g)

triangle-map-cone-fold :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  ( gap (map-prod f g) (diagonal X) (cone-fold f g c)) ~
  ( (map-cone-fold f g) ∘ (gap f g c))
triangle-map-cone-fold f g (pair p (pair q H)) z = refl

abstract
  is-pullback-cone-fold-is-pullback :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c →
    is-pullback (map-prod f g) (diagonal X) (cone-fold f g c)
  is-pullback-cone-fold-is-pullback f g c is-pb-c =
    is-equiv-comp
      ( gap (map-prod f g) (diagonal _) (cone-fold f g c))
      ( map-cone-fold f g)
      ( gap f g c)
      ( triangle-map-cone-fold f g c)
      ( is-pb-c)
      ( is-equiv-map-cone-fold f g)

abstract
  is-pullback-is-pullback-cone-fold :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback (map-prod f g) (diagonal X) (cone-fold f g c) →
    is-pullback f g c
  is-pullback-is-pullback-cone-fold f g c is-pb-fold =
    is-equiv-right-factor
      ( gap (map-prod f g) (diagonal _) (cone-fold f g c))
      ( map-cone-fold f g)
      ( gap f g c)
      ( triangle-map-cone-fold f g c)
      ( is-equiv-map-cone-fold f g)
      ( is-pb-fold)
```

```agda
prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  cone f g C → cone f' g' C' →
  cone (map-prod f f') (map-prod g g') (C × C')
pr1 (prod-cone f g f' g' (p , q , H) (p' , q' , H')) = map-prod p p'
pr1 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) = map-prod q q'
pr2 (pr2 (prod-cone f g f' g' (p , q , H) (p' , q' , H'))) =
  ( inv-htpy (map-prod-comp p p' f f')) ∙h
  ( ( htpy-map-prod H H') ∙h
    ( map-prod-comp q q' g g'))

map-prod-cone :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
  (canonical-pullback f g) × (canonical-pullback f' g') →
  canonical-pullback (map-prod f f') (map-prod g g')
map-prod-cone {A' = A'} {B'} f g f' g' =
  ( tot
    ( λ t →
      ( tot (λ s → eq-pair')) ∘
      ( map-interchange-Σ-Σ (λ y p y' → Id (f' (pr2 t)) (g' y'))))) ∘
  ( map-interchange-Σ-Σ (λ x t x' → Σ _ (λ y' → Id (f' x') (g' y'))))

triangle-map-prod-cone :
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (c : cone f g C)
  (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
  (gap (map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')) ~
  ((map-prod-cone f g f' g') ∘ (map-prod (gap f g c) (gap f' g' c')))
triangle-map-prod-cone {B' = B'}
  f g (pair p (pair q H)) f' g' (pair p' (pair q' H')) (pair z z') =
  eq-pair-Σ refl (eq-pair-Σ refl right-unit)

abstract
  is-equiv-map-prod-cone :
    {l1 l2 l3 l1' l2' l3' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
    (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X') →
    is-equiv (map-prod-cone f g f' g')
  is-equiv-map-prod-cone f g f' g' =
    is-equiv-comp
      ( map-prod-cone f g f' g')
      ( tot ( λ t →
        ( tot (λ s → eq-pair')) ∘
        ( map-interchange-Σ-Σ _)))
      ( map-interchange-Σ-Σ _)
      ( refl-htpy)
      ( is-equiv-map-interchange-Σ-Σ _)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ t → is-equiv-comp
          ( ( tot (λ s → eq-pair')) ∘
            ( map-interchange-Σ-Σ
              ( λ y p y' → Id (f' (pr2 t)) (g' y'))))
          ( tot (λ s → eq-pair'))
          ( map-interchange-Σ-Σ
            ( λ y p y' → Id (f' (pr2 t)) (g' y')))
          ( refl-htpy)
          ( is-equiv-map-interchange-Σ-Σ _)
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ s → is-equiv-comp
              ( eq-pair')
              ( eq-pair')
              ( id)
              ( refl-htpy)
              ( is-equiv-id)
              ( is-equiv-eq-pair
                ( map-prod f f' t)
                ( map-prod g g' s))))))

abstract
  is-pullback-prod-is-pullback-pair :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback f g c → is-pullback f' g' c' →
    is-pullback
      ( map-prod f f') (map-prod g g') (prod-cone f g f' g' c c')
  is-pullback-prod-is-pullback-pair f g c f' g' c' is-pb-c is-pb-c' =
    is-equiv-comp
      ( gap (map-prod f f') (map-prod g g') (prod-cone f g f' g' c c'))
      ( map-prod-cone f g f' g')
      ( map-prod (gap f g c) (gap f' g' c'))
      ( triangle-map-prod-cone f g c f' g' c')
      ( is-equiv-map-prod _ _ is-pb-c is-pb-c')
      ( is-equiv-map-prod-cone f g f' g')
  
abstract
  is-equiv-left-factor-is-equiv-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (d : D) →
    is-equiv (map-prod f g) → is-equiv f
  is-equiv-left-factor-is-equiv-map-prod f g d is-equiv-fg =
    is-equiv-is-contr-map
      ( λ x → is-contr-left-factor-prod
        ( fib f x)
        ( fib g d)
        ( is-contr-is-equiv'
          ( fib (map-prod f g) (pair x d))
          ( map-compute-fib-map-prod f g (pair x d))
          ( is-equiv-map-compute-fib-map-prod f g (pair x d))
          ( is-contr-map-is-equiv is-equiv-fg (pair x d))))

abstract
  is-equiv-right-factor-is-equiv-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) (c : C) →
    is-equiv (map-prod f g) → is-equiv g
  is-equiv-right-factor-is-equiv-map-prod f g c is-equiv-fg =
    is-equiv-is-contr-map
      ( λ y → is-contr-right-factor-prod
        ( fib f c)
        ( fib g y)
        ( is-contr-is-equiv'
          ( fib (map-prod f g) (pair c y))
          ( map-compute-fib-map-prod f g (pair c y))
          ( is-equiv-map-compute-fib-map-prod f g (pair c y))
          ( is-contr-map-is-equiv is-equiv-fg (pair c y))))

abstract
  is-pullback-left-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c') →
    canonical-pullback f' g' → is-pullback f g c
  is-pullback-left-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-left-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( prod-cone f g f' g' c c'))
      ( map-prod-cone f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-prod-cone f g c f' g' c')
        ( is-equiv-map-prod-cone f g f' g')
        ( is-pb-cc'))

abstract
  is-pullback-right-factor-is-pullback-prod :
    {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
    (f : A → X) (g : B → X) (c : cone f g C)
    (f' : A' → X') (g' : B' → X') (c' : cone f' g' C') →
    is-pullback
      ( map-prod f f')
      ( map-prod g g')
      ( prod-cone f g f' g' c c') →
    canonical-pullback f g → is-pullback f' g' c'
  is-pullback-right-factor-is-pullback-prod f g c f' g' c' is-pb-cc' t =
    is-equiv-right-factor-is-equiv-map-prod (gap f g c) (gap f' g' c') t
      ( is-equiv-right-factor
        ( gap
          ( map-prod f f')
          ( map-prod g g')
          ( prod-cone f g f' g' c c'))
        ( map-prod-cone f g f' g')
        ( map-prod (gap f g c) (gap f' g' c'))
        ( triangle-map-prod-cone f g c f' g' c')
        ( is-equiv-map-prod-cone f g f' g')
        ( is-pb-cc'))
```
