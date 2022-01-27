---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.homotopies where

open import foundation.functions using (_∘_; id)
open import foundation.universe-levels using (UU; Level; _⊔_)
open import foundation.identity-types using
  ( Id; refl; _∙_; concat; inv; assoc; left-unit; right-unit; left-inv;
    right-inv; ap; inv-con; con-inv; concat'; distributive-inv-concat; ap-inv;
    ap-id)
```

# Homotopies

```agda
_~_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → UU (l1 ⊔ l2)
f ~ g = (x : _) → Id (f x) (g x)

refl-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

{- Most of the time we get by with refl-htpy. However, sometimes Agda wants us
   to specify the implicit argument. The it is easier to call refl-htpy' than
   to use Agda's {f = ?} notation. -}
   
refl-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) → f ~ f
refl-htpy' f = refl-htpy

inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
inv-htpy H x = inv (H x)

_∙h_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ H K x = (H x) ∙ (K x)

concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (h : (x : A) → B x) → (g ~ h) → (f ~ h)
concat-htpy H h K x = concat (H x) (h x) (K x)

concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ g) → (f ~ h)
concat-htpy' f K H = H ∙h K

assoc-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} →
  (H : f ~ g) → (K : g ~ h) → (L : h ~ k) →
  ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
assoc-htpy H K L x = assoc (H x) (K x) (L x)

left-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
left-unit-htpy x = left-unit

right-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
right-unit-htpy x = right-unit

left-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → ((inv-htpy H) ∙h H) ~ refl-htpy
left-inv-htpy H x = left-inv (H x)

right-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → (H ∙h (inv-htpy H)) ~ refl-htpy
right-inv-htpy H x = right-inv (H x)

htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  inv-htpy-con :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → K ~ ((inv-htpy H) ∙h L)
  inv-htpy-con H K L M x = inv-con (H x) (K x) (L x) (M x)

  htpy-con-inv :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → H ~ (L ∙h (inv-htpy K))
  htpy-con-inv H K L M x = con-inv (H x) (K x) (L x) (M x)

  htpy-ap-concat :
    (H : f ~ g) (K K' : g ~ h) → K ~ K' → (H ∙h K) ~ (H ∙h K')
  htpy-ap-concat H K K' L x = ap (concat (H x) (h x)) (L x)

  htpy-ap-concat' :
    (H H' : f ~ g) (K : g ~ h) → H ~ H' → (H ∙h K) ~ (H' ∙h K)
  htpy-ap-concat' H H' K L x =
    ap (concat' _ (K x)) (L x)

  htpy-distributive-inv-concat :
    (H : f ~ g) (K : g ~ h) →
    (inv-htpy (H ∙h K)) ~ ((inv-htpy K) ∙h (inv-htpy H))
  htpy-distributive-inv-concat H K x = distributive-inv-concat (H x) (K x)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H H' : f ~ g}
  where

  htpy-ap-inv :
    H ~ H' → (inv-htpy H) ~ (inv-htpy H')
  htpy-ap-inv K x = ap inv (K x)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  htpy-left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
  htpy-left-whisk-inv-htpy g H x = ap-inv g (H x)

  htpy-right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  htpy-right-whisk-inv-htpy H f = refl-htpy
```

```agda
htpy-nat :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
htpy-nat H refl = right-unit

left-unwhisk :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = s

right-unwhisk :
  {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

htpy-red :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( htpy-nat H (H x)))
```

## Commuting squares

```agda
coherence-square :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (top : C → B) (left : C → A) (right : B → X) (bottom : A → X) →
  UU (l3 ⊔ l4)
coherence-square top left right bottom =
  (bottom ∘ left) ~ (right ∘ top)
```
