# Homotopies

```agda
module foundation-core.homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Idea

A **homotopy** between dependent functions `f` and `g` is a pointwise equality
between them.

## Definitions

### The type family of identifications between values of two dependent functions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} (f g : (x : X) → P x)
  where

  eq-value : X → UU l2
  eq-value x = (f x ＝ g x)

  {-# INLINE eq-value #-}

  map-compute-dependent-identification-eq-value :
    {x y : X} (p : x ＝ y) (q : eq-value x) (r : eq-value y) →
    coherence-square-identifications (apd f p) r (ap (tr P p) q) (apd g p) →
    dependent-identification eq-value p q r
  map-compute-dependent-identification-eq-value refl q r =
    inv ∘ (concat' r (right-unit ∙ ap-id q))
```

### The type family of identifications between values of two ordinary functions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f g : X → Y)
  where

  eq-value-function : X → UU l2
  eq-value-function = eq-value f g

  {-# INLINE eq-value-function #-}

  map-compute-dependent-identification-eq-value-function :
    {x y : X} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    coherence-square-identifications (ap f p) r q (ap g p) →
    dependent-identification eq-value-function p q r
  map-compute-dependent-identification-eq-value-function refl q r =
    inv ∘ concat' r right-unit

map-compute-dependent-identification-eq-value-id-id :
  {l1 : Level} {A : UU l1} {a b : A} (p : a ＝ b) (q : a ＝ a) (r : b ＝ b) →
  coherence-square-identifications p r q p →
  dependent-identification (eq-value id id) p q r
map-compute-dependent-identification-eq-value-id-id refl q r s =
  inv (s ∙ right-unit)
```

### Homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _~_ : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  f ~ g = (x : A) → eq-value f g x
```

## Properties

### Reflexivity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  refl-htpy : {f : (x : A) → B x} → f ~ f
  refl-htpy x = refl

  refl-htpy' : (f : (x : A) → B x) → f ~ f
  refl-htpy' f = refl-htpy
```

### Inverting homotopies

```agda
  inv-htpy : {f g : (x : A) → B x} → f ~ g → g ~ f
  inv-htpy H x = inv (H x)
```

### Concatenating homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _∙h_ : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
  (H ∙h K) x = (H x) ∙ (K x)

  concat-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → g ~ h → f ~ h
  concat-htpy H h K x = concat (H x) (h x) (K x)

  concat-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ h → f ~ g → f ~ h
  concat-htpy' f K H = H ∙h K

  concat-inv-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → f ~ h → g ~ h
  concat-inv-htpy = concat-htpy ∘ inv-htpy

  concat-inv-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    (g ~ h) → (f ~ h) → (f ~ g)
  concat-inv-htpy' f K = concat-htpy' f (inv-htpy K)
```

### Whiskering of homotopies

```agda
htpy-left-whisk :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (h : B → C) {f g : A → B} → f ~ g → (h ∘ f) ~ (h ∘ g)
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

htpy-right-whisk :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  {g h : (y : B) → C y} (H : g ~ h) (f : A → B) → (g ∘ f) ~ (h ∘ f)
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk
```

**Note**: The infix whiskering operators `_·l_` and `_·r_` use the
[middle dot](https://codepoints.net/U+00B7) `·` (agda-input: `\cdot`
`\centerdot`), as opposed to the infix homotopy concatenation operator `_∙h_`
which uses the [bullet operator](https://codepoints.net/U+2219) `∙` (agda-input:
`\.`). If these look the same in your editor, we suggest that you change your
font. For a reference, see [How to install](HOWTO-INSTALL.md).

### Horizontal composition of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f f' : A → B} {g g' : B → C}
  where

  htpy-comp-horizontal : (f ~ f') → (g ~ g') → (g ∘ f) ~ (g' ∘ f')
  htpy-comp-horizontal F G = (g ·l F) ∙h (G ·r f')

  htpy-comp-horizontal' : (f ~ f') → (g ~ g') → (g ∘ f) ~ (g' ∘ f')
  htpy-comp-horizontal' F G = (G ·r f) ∙h (g' ·l F)
```

### Transposition of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h) (M : (H ∙h K) ~ L)
  where

  inv-con-htpy : K ~ ((inv-htpy H) ∙h L)
  inv-con-htpy x = inv-con (H x) (K x) (L x) (M x)

  inv-htpy-inv-con-htpy : ((inv-htpy H) ∙h L) ~ K
  inv-htpy-inv-con-htpy = inv-htpy inv-con-htpy

  con-inv-htpy : H ~ (L ∙h (inv-htpy K))
  con-inv-htpy x = con-inv (H x) (K x) (L x) (M x)

  inv-htpy-con-inv-htpy : (L ∙h (inv-htpy K)) ~ H
  inv-htpy-con-inv-htpy = inv-htpy con-inv-htpy
```

### Associativity of concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h k : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : h ~ k)
  where

  assoc-htpy : ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
  assoc-htpy x = assoc (H x) (K x) (L x)

  inv-htpy-assoc-htpy : (H ∙h (K ∙h L)) ~ ((H ∙h K) ∙h L)
  inv-htpy-assoc-htpy = inv-htpy assoc-htpy
```

### Unit laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} {H : f ~ g}
  where

  left-unit-htpy : (refl-htpy ∙h H) ~ H
  left-unit-htpy x = left-unit

  inv-htpy-left-unit-htpy : H ~ (refl-htpy ∙h H)
  inv-htpy-left-unit-htpy = inv-htpy left-unit-htpy

  right-unit-htpy : (H ∙h refl-htpy) ~ H
  right-unit-htpy x = right-unit

  inv-htpy-right-unit-htpy : H ~ (H ∙h refl-htpy)
  inv-htpy-right-unit-htpy = inv-htpy right-unit-htpy
```

### Inverse laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g)
  where

  left-inv-htpy : ((inv-htpy H) ∙h H) ~ refl-htpy
  left-inv-htpy = left-inv ∘ H

  inv-htpy-left-inv-htpy : refl-htpy ~ ((inv-htpy H) ∙h H)
  inv-htpy-left-inv-htpy = inv-htpy left-inv-htpy

  right-inv-htpy : (H ∙h (inv-htpy H)) ~ refl-htpy
  right-inv-htpy = right-inv ∘ H

  inv-htpy-right-inv-htpy : refl-htpy ~ (H ∙h (inv-htpy H))
  inv-htpy-right-inv-htpy = inv-htpy right-inv-htpy
```

### Distributivity of `inv` over `concat` for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h)
  where

  distributive-inv-concat-htpy :
    (inv-htpy (H ∙h K)) ~ ((inv-htpy K) ∙h (inv-htpy H))
  distributive-inv-concat-htpy x = distributive-inv-concat (H x) (K x)

  inv-htpy-distributive-inv-concat-htpy :
    ((inv-htpy K) ∙h (inv-htpy H)) ~ (inv-htpy (H ∙h K))
  inv-htpy-distributive-inv-concat-htpy =
    inv-htpy distributive-inv-concat-htpy
```

### Naturality of homotopies with respect to identifications

```agda
nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  ((H x) ∙ (ap g p)) ＝ ((ap f p) ∙ (H y))
nat-htpy H refl = right-unit

inv-nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  ((ap f p) ∙ (H y)) ＝ ((H x) ∙ (ap g p))
inv-nat-htpy H p = inv (nat-htpy H p)

nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → ((H x) ∙ p) ＝ ((ap f p) ∙ (H y))
nat-htpy-id H refl = right-unit

inv-nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → ((ap f p) ∙ (H y)) ＝ ((H x) ∙ p)
inv-nat-htpy-id H p = inv (nat-htpy-id H p)
```

### A coherence for homotopies to the identity function

```agda
module _
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  where

  coh-htpy-id : (H ·r f) ~ (f ·l H)
  coh-htpy-id x = is-injective-concat' (H x) (nat-htpy-id H (H x))

  inv-htpy-coh-htpy-id : (f ·l H) ~ (H ·r f)
  inv-htpy-coh-htpy-id = inv-htpy coh-htpy-id
```

### Homotopies preserve the laws of the action on identity types

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

### Laws for whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
  left-whisk-inv-htpy g H x = ap-inv g (H x)

  inv-htpy-left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    inv-htpy (g ·l H) ~ (g ·l (inv-htpy H))
  inv-htpy-left-whisk-inv-htpy g H =
    inv-htpy (left-whisk-inv-htpy g H)

  right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  right-whisk-inv-htpy H f = refl-htpy

  inv-htpy-right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  inv-htpy-right-whisk-inv-htpy H f =
    inv-htpy (right-whisk-inv-htpy H f)
```

## Reasoning with homotopies

Homotopies can be constructed by equational reasoning in the following way:

```text
homotopy-reasoning
  f ~ g by htpy-1
    ~ h by htpy-2
    ~ i by htpy-3
```

The homotopy obtained in this way is `htpy-1 ∙h (htpy-2 ∙h htpy-3)`, i.e., it is
associated fully to the right.

```agda
infixl 1 homotopy-reasoning_
infixl 0 step-homotopy-reasoning

homotopy-reasoning_ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  (f : (x : X) → Y x) → f ~ f
homotopy-reasoning f = refl-htpy

step-homotopy-reasoning :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  {f g : (x : X) → Y x} → (f ~ g) →
  (h : (x : X) → Y x) → (g ~ h) → (f ~ h)
step-homotopy-reasoning p h q = p ∙h q

syntax step-homotopy-reasoning p h q = p ~ h by q
```

## See also

- We postulate that homotopies characterize identifications in (dependent)
  function types in the file
  [`foundation-core.function-extensionality`](foundation-core.function-extensionality.md).
