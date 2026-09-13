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

There are a few different ways we can define `ap-binary`. We could define it by
pattern matching on both `p` and `q`, but this leads to restricted computational
behavior. Instead, we define it as the upper concatenation in the Gray
interchanger diagram

```text
                      ap (r ↦ f x r) q
                 f x y -------------> f x y'
                   |                    |
                   |                    |
  ap (r ↦ f r y) p |                    | ap (r ↦ f r y') p
                   |                    |
                   ∨                    ∨
                 f x' y ------------> f x' y'.
                      ap (r ↦ f x' r) q
```

## Definition

### The binary action on identifications of binary functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') → f x y ＝ f x' y'
  ap-binary {x} {x'} p {y} {y'} q = ap (λ r → f r y) p ∙ ap (f x') q
```

## Properties

### The binary action on identifications in terms of the unary action on identifications

The binary action on identifications computes as a concatenation of applications
of the
[unary action on identifications of functions](foundation.action-on-identifications-functions.md):

```text
  ap-binary f p q ＝ ap (r ↦ f r y) p ∙ ap (r ↦ f x' r) q
```

and

```text
  ap-binary f p q ＝ ap (r ↦ f x r) q ∙ ap (r ↦ f r y') p.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  triangle-ap-binary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary f p q ＝ ap (λ r → f r y) p ∙ ap (f x') q
  triangle-ap-binary _ _ = refl

  triangle-ap-binary' :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary f p q ＝ ap (f x) q ∙ ap (λ r → f r y') p
  triangle-ap-binary' refl refl = refl
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
    {x x' : A} (p : x ＝ x') {y : B} → ap-binary f p refl ＝ ap (λ r → f r y) p
  right-unit-ap-binary refl = refl
```

### The binary action on identifications evaluated on the diagonal

The binary action on identifications evaluated on the diagonal computes as an
instance of unary action on identifications. Specifically, we have the following
uncurried [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                           (- ∘ Δ) × 1
       (A × A → B) × Path A --------> (A → B) × Path A
                |                             |
                |                             |
          1 × Δ |                             | ap
                |                             |
                ∨                             ∨
  (A × A → B) × Path A × Path A ----------> Path B.
                                 ap-binary
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → A → B)
  where

  ap-binary-diagonal :
    {x x' : A} (p : x ＝ x') → ap-binary f p p ＝ ap (λ r → f r r) p
  ap-binary-diagonal refl = refl
```

### The binary action on identifications distributes over identification concatenation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary-concat :
    {x y z : A} (p : x ＝ y) (p' : y ＝ z)
    {x' y' z' : B} (q : x' ＝ y') (q' : y' ＝ z') →
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
    {x x' : X} (p : x ＝ x') {y y' : Y} (q : y ＝ y') →
    ap-binary (λ x y → H (f x) (g y)) p q ＝ ap-binary H (ap f p) (ap g q)
  ap-binary-comp f g refl refl = refl

  ap-binary-comp-diagonal :
    {l4 : Level} {A' : UU l4} (f : A' → A) (g : A' → B)
    {x y : A'} (p : x ＝ y) →
    ap (λ z → H (f z) (g z)) p ＝ ap-binary H (ap f p) (ap g p)
  ap-binary-comp-diagonal f g p =
    ( inv (ap-binary-diagonal (λ x y → H (f x) (g y)) p)) ∙
    ( ap-binary-comp f g p p)

  ap-binary-comp' :
    {l4 : Level} {D : UU l4} (f : C → D)
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary (λ a b → f (H a b)) p q ＝ ap f (ap-binary H p q)
  ap-binary-comp' f refl refl = refl
```

### Computing the binary action on identifications when swapping argument order

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  ap-binary-permute :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
    ap-binary (λ y x → f x y) q p ＝ ap-binary f p q
  ap-binary-permute refl refl = refl
```

## See also

- [Action of binary dependent functions on identifications](foundation.action-on-identifications-binary-dependent-functions.md)
- [Action of ternary functions on identifications](foundation.action-on-identifications-ternary-functions.md)
- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of functions on higher identifications](foundation.action-on-higher-identifications-functions.md).
- [Action of dependent functions on identifications](foundation.action-on-identifications-dependent-functions.md).
