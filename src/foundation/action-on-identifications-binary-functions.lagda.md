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

Given a binary operation `f : A → B → C` and identifications `p : x ＝ x'` in
`A` and `q : y ＝ y'` in `B`, we obtain an identification

```text
  ap-binary f p q : f x y ＝ f x' y'
```

## Definition

### The binary action on identifications

```agda
ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y y' : B}
  (q : y ＝ y') → (f x y) ＝ (f x' y')
ap-binary f refl refl = refl

ap-binary-diagonal :
  {l1 l2 : Level} {A : UU l1}
  {B : UU l2} (f : A → A → B) →
  {x x' : A} (p : x ＝ x') →
  (ap-binary f p p) ＝ (ap (λ a → f a a) p)
ap-binary-diagonal f refl = refl

triangle-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1}
  {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  (ap-binary f p q) ＝ (ap (λ z → f z y) p ∙ ap (f x') q)
triangle-ap-binary f refl refl = refl

triangle-ap-binary' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  (ap-binary f p q) ＝ (ap (f x) q ∙ ap (λ z → f z y') p)
triangle-ap-binary' f refl refl = refl

left-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1}
  {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x : A} {y y' : B} (q : y ＝ y') →
  (ap-binary f refl q) ＝ (ap (f x) q)
left-unit-ap-binary f refl = refl

right-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1}
  {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y : B} →
  (ap-binary f p refl) ＝ (ap (λ z → f z y) p)
right-unit-ap-binary f refl = refl

ap-binary-comp :
  {l1 l2 l3 l4 l5 : Level} {X : UU l4} {Y : UU l5}
  {A : UU l1} {B : UU l2} {C : UU l3} (H : A → B → C)
  (f : X → A) (g : Y → B) {x0 x1 : X} (p : x0 ＝ x1)
  {y0 y1 : Y} (q : y0 ＝ y1) → (ap-binary (λ x y → H (f x) (g y)) p q) ＝
    ap-binary H (ap f p) (ap g q)
ap-binary-comp H f g refl refl = refl

ap-binary-comp-diagonal :
  {l1 l2 l3 l4 : Level} {A' : UU l4} {A : UU l1}
  {B : UU l2} {C : UU l3} (H : A → B → C)
  (f : A' → A) (g : A' → B) {a'0 a'1 : A'} (p : a'0 ＝ a'1) →
  (ap (λ z → H (f z) (g z)) p) ＝ ap-binary H (ap f p) (ap g p)
ap-binary-comp-diagonal H f g p =
  ( inv (ap-binary-diagonal (λ x y → H (f x) (g y)) p)) ∙
  ( ap-binary-comp H f g p p)

ap-binary-comp' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {C : UU l3} {D : UU l4} (f : C → D) (H : A → B → C)
  {a0 a1 : A} (p : a0 ＝ a1) {b0 b1 : B} (q : b0 ＝ b1) →
  (ap-binary (λ a b → f (H a b)) p q) ＝ (ap f (ap-binary H p q))
ap-binary-comp' f H refl refl = refl

ap-binary-permute :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A}
  {B : UU l2} {b0 b1 : B} {C : UU l3} (f : A → B → C) →
  (p : a0 ＝ a1) (q : b0 ＝ b1) →
  (ap-binary (λ y x → f x y) q p) ＝ (ap-binary f p q)
ap-binary-permute f refl refl = refl

ap-binary-concat :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 a2 : A}
  {B : UU l2} {b0 b1 b2 : B} {C : UU l3}
  (f : A → B → C) (p : a0 ＝ a1) (p' : a1 ＝ a2)
  (q : b0 ＝ b1) (q' : b1 ＝ b2) →
  (ap-binary f (p ∙ p') (q ∙ q')) ＝
    ((ap-binary f p q) ∙ (ap-binary f p' q'))
ap-binary-concat f refl refl refl refl = refl
```
