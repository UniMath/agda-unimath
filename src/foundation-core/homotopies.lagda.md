---
title: Homotopies
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation-core.homotopies where

open import foundation-core.functions
open import foundation-core.identity-types
open import foundation-core.universe-levels
```

## Idea

A homotopy of identifications is a pointwise equality between dependent functions.

## Definitions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} (f g : (x : X) → P x)
  where

  eq-value : X → UU l2
  eq-value x = (f x ＝ g x)

  tr-eq-value :
    {x y : X} (p : x ＝ y) (q : eq-value x) (r : eq-value y) →
    ((apd f p) ∙ r) ＝ ((ap (tr P p) q) ∙ (apd g p)) →
    tr eq-value p q ＝ r
  tr-eq-value refl q .(ap id q ∙ refl) refl = inv (right-unit ∙ ap-id q)

tr-eq-value-id-id :
  {l1 : Level} {A : UU l1} →
  {a b : A} (p : a ＝ b) (q : a ＝ a) (r : b ＝ b) →
  (p ∙ r) ＝ (q ∙ p) → (tr (eq-value id id) p q) ＝ r
tr-eq-value-id-id refl q r s = inv (s ∙ right-unit)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _~_ : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  f ~ g = (x : A) → eq-value f g x
```

## Properties

### Reflexivity

```
refl-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

refl-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) → f ~ f
refl-htpy' f = refl-htpy
```

### Inverting homotopies

```agda
inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  f ~ g → g ~ f
inv-htpy H x = inv (H x)
```

### Concatenating homotopies

```agda
_∙h_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  f ~ g → g ~ h → f ~ h
(H ∙h K) x = (H x) ∙ (K x)

concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  f ~ g → (h : (x : A) → B x) → g ~ h → f ~ h
concat-htpy H h K x = concat (H x) (h x) (K x)

concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  g ~ h → f ~ g → f ~ h
concat-htpy' f K H = H ∙h K
```

### Whiskering of homotopies

```agda
htpy-left-whisk :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (h : B → C) {f g : A → B} → f ~ g → (h ∘ f) ~ (h ∘ g)
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

htpy-right-whisk :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g h : B → C} (H : g ~ h) (f : A → B) → (g ∘ f) ~ (h ∘ f)
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk
```

## Properties

### Associativity of concatenation of homotopies

```agda
assoc-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h k : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : h ~ k) →
  ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
assoc-htpy H K L x = assoc (H x) (K x) (L x)
```

### Unit laws for homotopies

```agda
left-unit-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
left-unit-htpy x = left-unit

right-unit-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
right-unit-htpy x = right-unit
```

### Inverse laws for homotopies

```agda
left-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  (H : f ~ g) → ((inv-htpy H) ∙h H) ~ refl-htpy
left-inv-htpy H x = left-inv (H x)

right-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  (H : f ~ g) → (H ∙h (inv-htpy H)) ~ refl-htpy
right-inv-htpy H x = right-inv (H x)
```

### Distributivity of `inv` over `concat` for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  distributive-inv-concat-htpy :
    (H : f ~ g) (K : g ~ h) →
    (inv-htpy (H ∙h K)) ~ ((inv-htpy K) ∙h (inv-htpy H))
  distributive-inv-concat-htpy H K x = distributive-inv-concat (H x) (K x)
```

### Naturality of homotopies with respect to identifications

```agda
nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  ((H x) ∙ (ap g p)) ＝ ((ap f p) ∙ (H y))
nat-htpy H refl = right-unit

nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → ((H x) ∙ p) ＝ ((ap f p) ∙ (H y))
nat-htpy-id H refl = right-unit
```

### A coherence for homotopies to the identity function

```agda
coh-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id) → (H ·r f) ~ (f ·l H)
coh-htpy-id H x =
  is-injective-concat' (H x) (nat-htpy-id H (H x))
```

## See also

- We postulate that homotopy is equivalent to identity of functions in
  [foundation-core.function-extensionality](foundation-core.function-extensionality.html).