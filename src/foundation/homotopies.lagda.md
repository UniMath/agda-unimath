# Homotopies

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.homotopies where

open import foundation-core.homotopies public

open import foundation.identity-types using
  ( Id; refl; _∙_; concat; inv; assoc; left-unit; right-unit; left-inv;
    right-inv; ap; inv-con; con-inv; concat'; distributive-inv-concat; ap-inv;
    ap-id; is-injective-concat')
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A homotopy of identifications is a pointwise equality between dependent functions.

## Properties

### Associativity of concatenation of homotopies

```agda
assoc-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} →
  (H : f ~ g) → (K : g ~ h) → (L : h ~ k) →
  ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
assoc-htpy H K L x = assoc (H x) (K x) (L x)
```

### Unit laws for homotopies

```agda
left-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
left-unit-htpy x = left-unit

right-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
right-unit-htpy x = right-unit
```

### Inverse laws for homotopies

```agda
left-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → ((inv-htpy H) ∙h H) ~ refl-htpy
left-inv-htpy H x = left-inv (H x)

right-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → (H ∙h (inv-htpy H)) ~ refl-htpy
right-inv-htpy H x = right-inv (H x)
```

### Whiskering of homotopies

```agda
htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((λ x → h (f x)) ~ (λ x → h (g x)))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((λ x → g (f x)) ~ (λ x → h (f x)))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk
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

### Transpositions of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  inv-con-htpy :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → K ~ ((inv-htpy H) ∙h L)
  inv-con-htpy H K L M x = inv-con (H x) (K x) (L x) (M x)

  con-inv-htpy :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → H ~ (L ∙h (inv-htpy K))
  con-inv-htpy H K L M x = con-inv (H x) (K x) (L x) (M x)
```

### Homotopies preserve the laws of the acion on identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  ap-concat-htpy :
    (H : f ~ g) (K K' : g ~ h) → K ~ K' → (H ∙h K) ~ (H ∙h K')
  ap-concat-htpy H K K' L x = ap (concat (H x) (h x)) (L x)

  ap-concat-htpy' :
    (H H' : f ~ g) (K : g ~ h) → H ~ H' → (H ∙h K) ~ (H' ∙h K)
  ap-concat-htpy' H H' K L x =
    ap (concat' _ (K x)) (L x)
    
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H H' : f ~ g}
  where

  ap-inv-htpy :
    H ~ H' → (inv-htpy H) ~ (inv-htpy H')
  ap-inv-htpy K x = ap inv (K x)
```

### Whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
  left-whisk-inv-htpy g H x = ap-inv g (H x)

  right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  right-whisk-inv-htpy H f = refl-htpy
```

### Naturality of homotopies with respect to identifications

```agda
nat-htpy :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
nat-htpy H refl = right-unit
```

