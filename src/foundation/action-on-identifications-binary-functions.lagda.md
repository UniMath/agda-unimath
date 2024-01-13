# The binary action on identifications of binary functions

```agda
module foundation.action-on-identifications-binary-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Given a binary operation `f : A → B → C` and
[identifications](foundation-core.identity-types.md) `p : x ＝ x'` in `A` and
`q : y ＝ y'` in `B`, we obtain an identification

```text
  ap-binary f p q : f x y ＝ f x' y'
```

we call this the
{{#concept "binary action on identifications of binary functions" Agda=ap-binary}}.

## Definition

### The binary action on identifications of binary functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') → f x y ＝ f x' y'
  ap-binary {x} refl = ap (f x)
```

## Properties

### The binary action on identifications in terms of the unary action on identifications

The binary action on identifications computes as a concatenation of applications
of the
[unary action on identifications of functions](foundation.action-on-identifications-functions.md):

```text
  ap-binary f p q ＝ ap (f (-) y) p ∙ ap (f x' (-)) q
```

and

```text
  ap-binary f p q ＝ ap (f x (-)) q ∙ ap (f (-) y') p.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  triangle-ap-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary f p q ＝ ap (λ z → f z y) p ∙ ap (f x') q
  triangle-ap-binary refl _ = refl

  triangle-ap-binary' :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary f p q ＝ ap (f x) q ∙ ap (λ z → f z y') p
  triangle-ap-binary' refl _ = inv right-unit
```

### The unit laws for the binary action on identifications of binary functions

The binary action on identifications of binary functions evaluated at a
reflexivity computes as an instance of unary action on identifications of
(unary) functions.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  left-unit-ap-binary :
    {x : A} {y y' : B} (q : y ＝ y') → ap-binary f refl q ＝ ap (f x) q
  left-unit-ap-binary _ = refl

  right-unit-ap-binary :
    {x x' : A} (p : x ＝ x') {y : B} → ap-binary f p refl ＝ ap (λ z → f z y) p
  right-unit-ap-binary refl = refl
```

### The binary action on identifications evaluated on the diagonal

The binary action on identifications evaluated on the diagonal computes as an
instance of unary action on identifications. Specifically, we have the following
[commuting square](foundation-core.commuting-squares-maps.md)

```text
                            Δ(-) ∘ 1
       (A → A → B) × Path A --------> (A → B) × Path A
                |                             |
                |                             |
          1 × Δ |                             | ap
                |                             |
                v                             v
  (A → A → B) × Path A × Path A ----------> Path B.
                                 ap-binary
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → A → B)
  where

  ap-binary-diagonal :
    {x x' : A} (p : x ＝ x') → ap-binary f p p ＝ ap (λ a → f a a) p
  ap-binary-diagonal refl = refl
```

### The binary action on identifications distributes over identification concatenation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary-concat :
    {a0 a1 a2 : A} (p : a0 ＝ a1) (p' : a1 ＝ a2)
    {b0 b1 b2 : B} (q : b0 ＝ b1) (q' : b1 ＝ b2) →
    ap-binary f (p ∙ p') (q ∙ q') ＝ ap-binary f p q ∙ ap-binary f p' q'
  ap-binary-concat refl _ refl _ = refl
```

### The binary action on identifications distributes over function composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (H : A → B → C)
  where

  ap-binary-comp :
    {l4 l5 : Level} {X : UU l4} {Y : UU l5} (f : X → A) (g : Y → B)
    {x0 x1 : X} (p : x0 ＝ x1) {y0 y1 : Y} (q : y0 ＝ y1) →
    ap-binary (λ x y → H (f x) (g y)) p q ＝ ap-binary H (ap f p) (ap g q)
  ap-binary-comp f g refl refl = refl

  ap-binary-comp-diagonal :
    {l4 : Level} {A' : UU l4} (f : A' → A) (g : A' → B)
    {a'0 a'1 : A'} (p : a'0 ＝ a'1) →
    ap (λ z → H (f z) (g z)) p ＝ ap-binary H (ap f p) (ap g p)
  ap-binary-comp-diagonal f g p =
    ( inv (ap-binary-diagonal (λ x y → H (f x) (g y)) p)) ∙
    ( ap-binary-comp f g p p)

  ap-binary-comp' :
    {l4 : Level} {D : UU l4} (f : C → D)
    {a0 a1 : A} (p : a0 ＝ a1) {b0 b1 : B} (q : b0 ＝ b1) →
    ap-binary (λ a b → f (H a b)) p q ＝ ap f (ap-binary H p q)
  ap-binary-comp' f refl refl = refl
```

### Computing the binary action on identifications when swapping argument order

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary-permute :
    {a0 a1 : A} (p : a0 ＝ a1) {b0 b1 : B} (q : b0 ＝ b1) →
    ap-binary (λ y x → f x y) q p ＝ ap-binary f p q
  ap-binary-permute refl refl = refl
```
