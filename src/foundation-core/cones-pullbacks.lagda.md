---
title: Cones on pullback diagrams
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.cones-pullbacks where

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.universe-levels

open import foundation.homotopies
open import foundation.structure-identity-principle
```

## Definitions

### Cospans

A cospan is a pair of functions with a common codomain

```agda
cospan :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ (l2 ⊔ (lsuc l)))
cospan l A B =
  Σ (UU l) (λ X → (A → X) × (B → X))
```

### Cones on cospans

A cone on a cospan with a vertex C is a pair of functions from C into the domains of the maps in the cospan, equipped with a homotopy witnessing that the resulting square commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where
   
  cone : {l4 : Level} → UU l4 → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
  cone C = Σ (C → A) (λ p → Σ (C → B) (λ q → coherence-square q p g f))

  {- A map into the vertex of a cone induces a new cone. -}
  
  cone-map :
    {l4 l5 : Level} {C : UU l4} {C' : UU l5} → cone C → (C' → C) → cone C'
  pr1 (cone-map c h) = (pr1 c) ∘ h
  pr1 (pr2 (cone-map c h)) = pr1 (pr2 c) ∘ h
  pr2 (pr2 (cone-map c h)) = pr2 (pr2 c) ·r h
```

### Identifications of cones

Next we characterize the identity type of the type of cones with a given vertex C. Note that in the definition of htpy-cone we do not use pattern matching on the cones c and c'. This is to ensure that the type htpy-cone f g c c' is a Σ-type for any c and c', not just for c and c' of the form (pair p (pair q H)) and (pair p' (pair q' H')) respectively.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where
  
  coherence-htpy-cone :
    (c c' : cone f g C) (K : (pr1 c) ~ (pr1 c'))
    (L : (pr1 (pr2 c)) ~ (pr1 (pr2 c'))) → UU (l4 ⊔ l3)
  coherence-htpy-cone c c' K L =
    ( (pr2 (pr2 c)) ∙h (htpy-left-whisk g L)) ~
    ( (htpy-left-whisk f K) ∙h (pr2 (pr2 c')))

  htpy-cone : cone f g C → cone f g C → UU (l1 ⊔ (l2 ⊔ (l3 ⊔ l4)))
  htpy-cone c c' =
    Σ ( (pr1 c) ~ (pr1 c'))
      ( λ K → Σ ((pr1 (pr2 c)) ~ (pr1 (pr2 c')))
        ( λ L → coherence-htpy-cone c c' K L))

  refl-htpy-cone : (c : cone f g C) → htpy-cone c c
  pr1 (refl-htpy-cone c) = refl-htpy
  pr1 (pr2 (refl-htpy-cone c)) = refl-htpy
  pr2 (pr2 (refl-htpy-cone c)) = right-unit-htpy
      
  htpy-eq-cone : (c c' : cone f g C) → c ＝ c' → htpy-cone c c'
  htpy-eq-cone c .c refl = refl-htpy-cone c

  extensionality-cone : (c d : cone f g C) → (c ＝ d) ≃ htpy-cone c d
  extensionality-cone (pair p (pair q H)) =
    extensionality-Σ
      ( λ {p'} qH' K →
        Σ ( q ~ pr1 qH')
            ( coherence-htpy-cone (pair p (pair q H)) (pair p' qH') K))
      ( refl-htpy)
      ( pair refl-htpy right-unit-htpy)
      ( λ p' → equiv-funext)
      ( extensionality-Σ
        ( λ {q'} H' →
          coherence-htpy-cone
            ( pair p (pair q H))
            ( pair p (pair q' H'))
            ( refl-htpy))
        ( refl-htpy)
        ( right-unit-htpy)
        ( λ q' → equiv-funext)
        ( λ H' → equiv-concat-htpy right-unit-htpy H' ∘e equiv-funext))

  is-contr-total-htpy-cone :
    (c : cone f g C) → is-contr (Σ (cone f g C) (htpy-cone c))
  is-contr-total-htpy-cone c =
     fundamental-theorem-id' c
       ( refl-htpy-cone c)
       ( λ c' → map-equiv (extensionality-cone c c'))
       ( λ c' → is-equiv-map-equiv (extensionality-cone c c'))

  eq-htpy-cone :
    (c c' : cone f g C) → htpy-cone c c' → c ＝ c'
  eq-htpy-cone c c' = map-inv-equiv (extensionality-cone c c')
```

### Horizontal composition of cones

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
```

### Vertical composition of cones

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
```

### The swapping function on cones

```agda
swap-cone :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) → cone f g C → cone g f C
swap-cone f g (pair p (pair q H)) = triple q p (inv-htpy H)
```
