# Transport

```agda
module foundation-core.transport where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Given a type family `B` over `A`, an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A` and an
element `b : B x`, we can **transport** the element `b` along the identification
`p` to obtain an element `tr B p b : B y`.

The fact that `tr B p` is an [equivalence](foundation-core.equivalences.md) is
recorded in [`foundation.transport`](foundation.transport.md).

## Definition

### Transport

```agda
tr :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A} (p : x ＝ y) → B x → B y
tr B refl b = b
```

### Laws for transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  tr-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) (b : B x) →
    tr B (p ∙ q) b ＝ tr B q (tr B p b)
  tr-concat refl q b = refl

  eq-transpose-tr :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    v ＝ (tr B p u) → (tr B (inv p) v) ＝ u
  eq-transpose-tr refl q = q

  eq-transpose-tr' :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    (tr B p u) ＝ v → u ＝ (tr B (inv p) v)
  eq-transpose-tr' refl q = q

tr-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : A → C) (g : (x : A) → B x → D (f x)) {x y : A} (p : x ＝ y) (z : B x) →
  (tr D (ap f p) (g x z)) ＝ (g y (tr B p z))
tr-ap f g refl z = refl

preserves-tr :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) {i j : I} (p : i ＝ j) (x : A i) →
  f j (tr A p x) ＝ tr B p (f i x)
preserves-tr f refl x = refl

tr-Id-left :
  {l : Level} {A : UU l} {a b c : A} (q : b ＝ c) (p : b ＝ a) →
  (tr (_＝ a) q p) ＝ ((inv q) ∙ p)
tr-Id-left refl p = refl

tr-Id-right :
  {l : Level} {A : UU l} {a b c : A} (q : b ＝ c) (p : a ＝ b) →
  tr (a ＝_) q p ＝ (p ∙ q)
tr-Id-right refl refl = refl
```
