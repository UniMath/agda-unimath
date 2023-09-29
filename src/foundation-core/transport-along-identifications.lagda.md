# Transport along identifications

```agda
module foundation-core.transport-along-identifications where
```

<details><summary>Imports</summary>

```agda
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
recorded in
[`foundation.transport-along-identifications`](foundation.transport-along-identifications.md).

## Definition

### Transport

```agda
tr :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A} (p : x ＝ y) → B x → B y
tr B refl b = b
```

## Properties

### Transport preserves concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  tr-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) (b : B x) →
    tr B (p ∙ q) b ＝ tr B q (tr B p b)
  tr-concat refl q b = refl
```

### Transposing transport along the inverse of an identification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  eq-transpose-tr :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    v ＝ tr B p u → tr B (inv p) v ＝ u
  eq-transpose-tr refl q = q

  eq-transpose-tr' :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    tr B p u ＝ v → u ＝ tr B (inv p) v
  eq-transpose-tr' refl q = q
```

### Every family of maps preserves transport

```agda
preserves-tr :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i)
  {i j : I} (p : i ＝ j) (x : A i) →
  f j (tr A p x) ＝ tr B p (f i x)
preserves-tr f refl x = refl
```

### Computing maps out of identity types as transports

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a : A}
  (f : (x : A) → (a ＝ x) → B x)
  where

  compute-map-out-of-identity-type :
    (x : A) (p : a ＝ x) → f x p ＝ tr B p (f a refl)
  compute-map-out-of-identity-type x refl = refl
```
