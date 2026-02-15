# The ternary action on identifications of ternary functions

```agda
module foundation.action-on-identifications-ternary-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Given a ternary operation `f : A → B → C → D` and
[identifications](foundation-core.identity-types.md) `p : x ＝ x'` in `A`,
`q : y ＝ y'` in `B`, and `r : z ＝ z'` in `C`, we obtain an identification

```text
  ap-ternary f p q r : f x y z ＝ f x' y' z'
```

we call this the
{{#concept "ternary action on identifications of ternary functions" Agda=ap-ternary}}.

## Definition

### The ternary action on identifications of ternary functions

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B → C → D)
  where

  ap-ternary :
    {x x' : A} (p : x ＝ x')
    {y y' : B} (q : y ＝ y')
    {z z' : C} (r : z ＝ z') →
    f x y z ＝ f x' y' z'
  ap-ternary {x} {x'} p {y} {y'} q {z} {z'} r =
    ap (λ t → f t y z) p ∙ ap-binary (f x') q r
```

## Properties

### The ternary action on identifications in terms of unary and binary action

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B → C → D)
  where

  triangle-ap-ternary :
    {x x' : A} (p : x ＝ x')
    {y y' : B} (q : y ＝ y')
    {z z' : C} (r : z ＝ z') →
    ap-ternary f p q r ＝ ap (λ t → f t y z) p ∙ ap-binary (f x') q r
  triangle-ap-ternary _ _ _ = refl

  triangle-ap-ternary' :
    {x x' : A} (p : x ＝ x')
    {y y' : B} (q : y ＝ y')
    {z z' : C} (r : z ＝ z') →
    ap-ternary f p q r ＝ ap-binary (f x) q r ∙ ap (λ t → f t y' z') p
  triangle-ap-ternary' refl refl refl = refl
```

### Unit laws for the ternary action on identifications

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B → C → D)
  where

  left-unit-ap-ternary :
    {x : A} {y y' : B} (q : y ＝ y') {z z' : C} (r : z ＝ z') →
    ap-ternary f refl q r ＝ ap-binary (f x) q r
  left-unit-ap-ternary _ _ = refl

  middle-unit-ap-ternary :
    {x x' : A} (p : x ＝ x') {y : B} {z z' : C} (r : z ＝ z') →
    ap-ternary f p refl r ＝ ap-binary (λ s t → f s y t) p r
  middle-unit-ap-ternary refl refl = refl

  right-unit-ap-ternary :
    {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') {z : C} →
    ap-ternary f p q refl ＝ ap-binary (λ s t → f s t z) p q
  right-unit-ap-ternary refl refl = refl
```

### The ternary action on identifications evaluated on the diagonal

```agda
module _
  {l1 l2 : Level} {A : UU l1} {D : UU l2} (f : A → A → A → D)
  where

  ap-ternary-diagonal :
    {x x' : A} (p : x ＝ x') → ap-ternary f p p p ＝ ap (λ t → f t t t) p
  ap-ternary-diagonal refl = refl
```

### The ternary action on identifications distributes over concatenation

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B → C → D)
  where

  ap-ternary-concat :
    {x y z : A} (p : x ＝ y) (p' : y ＝ z)
    {x' y' z' : B} (q : x' ＝ y') (q' : y' ＝ z')
    {x'' y'' z'' : C} (r : x'' ＝ y'') (r' : y'' ＝ z'') →
    ap-ternary f (p ∙ p') (q ∙ q') (r ∙ r') ＝
    ap-ternary f p q r ∙ ap-ternary f p' q' r'
  ap-ternary-concat refl _ refl _ refl _ = refl
```

### The ternary action on identifications distributes over function composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (H : A → B → C → D)
  where

  ap-ternary-comp :
    {l5 l6 l7 : Level} {X : UU l5} {Y : UU l6} {Z : UU l7}
    (f : X → A) (g : Y → B) (h : Z → C)
    {x x' : X} (p : x ＝ x')
    {y y' : Y} (q : y ＝ y')
    {z z' : Z} (r : z ＝ z') →
    ap-ternary (λ x y z → H (f x) (g y) (h z)) p q r ＝
    ap-ternary H (ap f p) (ap g q) (ap h r)
  ap-ternary-comp f g h refl refl refl = refl

  ap-ternary-comp-diagonal :
    {l5 : Level} {A' : UU l5}
    (f : A' → A) (g : A' → B) (h : A' → C)
    {x y : A'} (p : x ＝ y) →
    ap (λ t → H (f t) (g t) (h t)) p ＝
    ap-ternary H (ap f p) (ap g p) (ap h p)
  ap-ternary-comp-diagonal f g h p =
    ( inv (ap-ternary-diagonal (λ x y z → H (f x) (g y) (h z)) p)) ∙
    ( ap-ternary-comp f g h p p p)

  ap-ternary-comp' :
    {l5 : Level} {E : UU l5} (f : D → E)
    {x x' : A} (p : x ＝ x')
    {y y' : B} (q : y ＝ y')
    {z z' : C} (r : z ＝ z') →
    ap-ternary (λ a b c → f (H a b c)) p q r ＝ ap f (ap-ternary H p q r)
  ap-ternary-comp' f refl refl refl = refl
```

### Computing the ternary action on identifications when swapping the first two arguments

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B → C → D)
  where

  ap-ternary-permute :
    {x x' : A} (p : x ＝ x')
    {y y' : B} (q : y ＝ y')
    {z z' : C} (r : z ＝ z') →
    ap-ternary (λ y x z → f x y z) q p r ＝ ap-ternary f p q r
  ap-ternary-permute refl refl refl = refl
```

## See also

- [Action of binary functions on identifications](foundation.action-on-identifications-binary-functions.md)
- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of dependent functions on identifications](foundation.action-on-identifications-dependent-functions.md).
