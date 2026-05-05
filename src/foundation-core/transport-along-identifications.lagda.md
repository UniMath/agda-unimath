# Transport along identifications

```agda
module foundation-core.transport-along-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.function-types
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

## Definitions

### Transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  tr : x ＝ y → B x → B y
  tr refl b = b

  inv-tr : y ＝ x → B x → B y
  inv-tr p = tr (inv p)
```

## Properties

### The dependent action of a family of maps over a map on identifications in the base type

```agda
tr-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : A → C) (g : (x : A) → B x → D (f x))
  {x y : A} (p : x ＝ y) (z : B x) →
  tr D (ap f p) (g x z) ＝ g y (tr B p z)
tr-ap f g refl z = refl
```

### Every family of maps preserves transport

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i)
  where

  preserves-tr :
    {i j : I} (p : i ＝ j) (x : A i) →
    f j (tr A p x) ＝ tr B p (f i x)
  preserves-tr refl x = refl

  inv-preserves-tr :
    {i j : I} (p : i ＝ j) (x : A i) →
    tr B p (f i x) ＝ f j (tr A p x)
  inv-preserves-tr p x = inv (preserves-tr p x)

  compute-preserves-tr :
    {i j : I} (p : i ＝ j) (x : A i) →
    preserves-tr p x ＝
    inv (tr-ap id f p x) ∙ ap (λ q → tr B q (f i x)) (ap-id p)
  compute-preserves-tr refl x = refl
```

### Substitution law for transport

```agda
substitution-law-tr :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (B : A → UU l3) (f : X → A)
  {x y : X} (p : x ＝ y) {x' : B (f x)} →
  tr B (ap f p) x' ＝ tr (B ∘ f) p x'
substitution-law-tr B f p {x'} = tr-ap f (λ _ → id) p x'
```

### Transport preserves concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  tr-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) (b : B x) →
    tr B (p ∙ q) b ＝ tr B q (tr B p b)
  tr-concat refl q b = refl

  comp-tr :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) (b : B x) →
    tr B q (tr B p b) ＝ tr B (p ∙ q) b
  comp-tr p q b = inv (tr-concat p q b)
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

### Computing maps out of identity types as transports

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a : A}
  (f : (x : A) → a ＝ x → B x)
  where

  compute-map-out-of-identity-type :
    (x : A) (p : a ＝ x) → f x p ＝ tr B p (f a refl)
  compute-map-out-of-identity-type x refl = refl
```

### Computing transport in the type family of identifications with a fixed target

```agda
tr-Id-left :
  {l : Level} {A : UU l} {a b c : A} (q : b ＝ c) (p : b ＝ a) →
  tr (_＝ a) q p ＝ inv q ∙ p
tr-Id-left refl p = refl
```

### Computing transport in the type family of identifications with a fixed source

```agda
tr-Id-right :
  {l : Level} {A : UU l} {a b c : A} (q : b ＝ c) (p : a ＝ b) →
  tr (a ＝_) q p ＝ p ∙ q
tr-Id-right refl p = inv right-unit
```
