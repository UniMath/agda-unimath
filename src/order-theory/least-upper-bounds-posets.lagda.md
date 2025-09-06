# Least upper bounds in posets

```agda
module order-theory.least-upper-bounds-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

A **least upper bound** of `a` and `b` in a poset `P` is an element `x` such
that the logical equivalence

```text
  ((a ≤ y) ∧ (b ≤ y)) ⇔ (x ≤ y)
```

holds for every element `y` in `P`. Similarly, a **least upper bound** of a
family `a : I → P` of elements of `P` is an element `x` of `P` such that the
logical equivalence

```text
  (∀ᵢ (aᵢ ≤ y)) ⇔ (x ≤ y)
```

holds for every element `y` in `P`.

## Definitions

### The predicate of being a least binary upper bound of two elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b : type-Poset P)
  where

  is-least-binary-upper-bound-Poset-Prop : type-Poset P → Prop (l1 ⊔ l2)
  is-least-binary-upper-bound-Poset-Prop x =
    Π-Prop
      ( type-Poset P)
      ( λ y →
        iff-Prop
          ( is-binary-upper-bound-Poset-Prop P a b y)
          ( leq-prop-Poset P x y))

  is-least-binary-upper-bound-Poset : type-Poset P → UU (l1 ⊔ l2)
  is-least-binary-upper-bound-Poset x =
    type-Prop (is-least-binary-upper-bound-Poset-Prop x)

  is-prop-is-least-binary-upper-bound-Poset :
    (x : type-Poset P) →
    is-prop (is-least-binary-upper-bound-Poset x)
  is-prop-is-least-binary-upper-bound-Poset x =
    is-prop-type-Prop (is-least-binary-upper-bound-Poset-Prop x)

module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b : type-Poset P}
  where

  forward-implication-is-least-binary-upper-bound-Poset :
    {x y : type-Poset P} →
    is-least-binary-upper-bound-Poset P a b x →
    is-binary-upper-bound-Poset P a b y → leq-Poset P x y
  forward-implication-is-least-binary-upper-bound-Poset {x} {y} H =
    forward-implication (H y)

  backward-implication-is-least-binary-upper-bound-Poset :
    {x y : type-Poset P} →
    is-least-binary-upper-bound-Poset P a b x →
    leq-Poset P x y → is-binary-upper-bound-Poset P a b y
  backward-implication-is-least-binary-upper-bound-Poset {x} {y} H =
    backward-implication (H y)

  prove-is-least-binary-upper-bound-Poset :
    {x : type-Poset P} →
    is-binary-upper-bound-Poset P a b x →
    ( (y : type-Poset P) →
      is-binary-upper-bound-Poset P a b y → leq-Poset P x y) →
    is-least-binary-upper-bound-Poset P a b x
  pr1 (prove-is-least-binary-upper-bound-Poset H K y) L = K y L
  pr2 (prove-is-least-binary-upper-bound-Poset H K y) L =
    is-binary-upper-bound-leq-Poset P H L

  is-binary-upper-bound-is-least-binary-upper-bound-Poset :
    {x : type-Poset P} →
    is-least-binary-upper-bound-Poset P a b x →
    is-binary-upper-bound-Poset P a b x
  is-binary-upper-bound-is-least-binary-upper-bound-Poset {x} H =
    backward-implication-is-least-binary-upper-bound-Poset H
      ( refl-leq-Poset P x)

  leq-left-is-least-binary-upper-bound-Poset :
    {x : type-Poset P} →
    is-least-binary-upper-bound-Poset P a b x →
    leq-Poset P a x
  leq-left-is-least-binary-upper-bound-Poset H =
    leq-left-is-binary-upper-bound-Poset P
      ( is-binary-upper-bound-is-least-binary-upper-bound-Poset H)

  leq-right-is-least-binary-upper-bound-Poset :
    {x : type-Poset P} →
    is-least-binary-upper-bound-Poset P a b x →
    leq-Poset P b x
  leq-right-is-least-binary-upper-bound-Poset H =
    leq-right-is-binary-upper-bound-Poset P
      ( is-binary-upper-bound-is-least-binary-upper-bound-Poset H)
```

### The least upper bound of `a` and `b` is the least upper bound of `b` and `a`

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b c : type-Poset P)
  where

  symmetric-is-least-binary-upper-bound-Poset :
    is-least-binary-upper-bound-Poset P a b c →
    is-least-binary-upper-bound-Poset P b a c
  pr1 (symmetric-is-least-binary-upper-bound-Poset lub-c d) lub-d =
    forward-implication
      ( lub-c d)
      ( leq-right-is-binary-upper-bound-Poset P lub-d ,
        leq-left-is-binary-upper-bound-Poset P lub-d)
  pr1 (pr2 (symmetric-is-least-binary-upper-bound-Poset lub-c d) c≤d) =
    leq-right-is-binary-upper-bound-Poset P (backward-implication (lub-c d) c≤d)
  pr2 (pr2 (symmetric-is-least-binary-upper-bound-Poset lub-c d) c≤d) =
    leq-left-is-binary-upper-bound-Poset P (backward-implication (lub-c d) c≤d)
```

### The proposition that two elements have a least upper bound

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b : type-Poset P)
  where

  has-least-binary-upper-bound-Poset : UU (l1 ⊔ l2)
  has-least-binary-upper-bound-Poset =
    Σ (type-Poset P) (is-least-binary-upper-bound-Poset P a b)

  all-elements-equal-has-least-binary-upper-bound-Poset :
    all-elements-equal has-least-binary-upper-bound-Poset
  all-elements-equal-has-least-binary-upper-bound-Poset (u , H) (v , K) =
    eq-type-subtype
      ( is-least-binary-upper-bound-Poset-Prop P a b)
      ( antisymmetric-leq-Poset P u v
        ( forward-implication-is-least-binary-upper-bound-Poset P H
          ( is-binary-upper-bound-is-least-binary-upper-bound-Poset P K))
        ( forward-implication-is-least-binary-upper-bound-Poset P K
          ( is-binary-upper-bound-is-least-binary-upper-bound-Poset P H)))

  is-prop-has-least-binary-upper-bound-Poset :
    is-prop has-least-binary-upper-bound-Poset
  is-prop-has-least-binary-upper-bound-Poset =
    is-prop-all-elements-equal
      all-elements-equal-has-least-binary-upper-bound-Poset

  has-least-binary-upper-bound-prop-Poset : Prop (l1 ⊔ l2)
  pr1 has-least-binary-upper-bound-prop-Poset =
    has-least-binary-upper-bound-Poset
  pr2 has-least-binary-upper-bound-prop-Poset =
    is-prop-has-least-binary-upper-bound-Poset

module _
  {l1 l2 : Level} (P : Poset l1 l2) {a b : type-Poset P}
  where

  eq-is-least-binary-upper-bound-Poset :
    {x y : type-Poset P} →
    is-least-binary-upper-bound-Poset P a b x →
    is-least-binary-upper-bound-Poset P a b y →
    x ＝ y
  eq-is-least-binary-upper-bound-Poset {x} {y} H K =
    ap
      ( pr1)
      ( all-elements-equal-has-least-binary-upper-bound-Poset P a b
        ( x , H)
        ( y , K))
```

### The property of having a least binary upper bound is symmetric

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b : type-Poset P)
  where

  symmetric-has-least-binary-upper-bound-Poset :
    has-least-binary-upper-bound-Poset P a b →
    has-least-binary-upper-bound-Poset P b a
  pr1 (symmetric-has-least-binary-upper-bound-Poset (lub , is-lub)) = lub
  pr2 (symmetric-has-least-binary-upper-bound-Poset (lub , is-lub)) =
    symmetric-is-least-binary-upper-bound-Poset P a b lub is-lub
```

### Least upper bounds of families of elements

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (a : I → type-Poset P)
  where

  is-least-upper-bound-family-of-elements-prop-Poset :
    type-Poset P → Prop (l1 ⊔ l2 ⊔ l3)
  is-least-upper-bound-family-of-elements-prop-Poset x =
    Π-Prop
      ( type-Poset P)
      ( λ y →
        iff-Prop
          ( Π-Prop I (λ i → leq-prop-Poset P (a i) y))
          ( leq-prop-Poset P x y))

  is-least-upper-bound-family-of-elements-Poset :
    type-Poset P → UU (l1 ⊔ l2 ⊔ l3)
  is-least-upper-bound-family-of-elements-Poset z =
    type-Prop (is-least-upper-bound-family-of-elements-prop-Poset z)

  is-prop-is-least-upper-bound-family-of-elements-Poset :
    (z : type-Poset P) →
    is-prop (is-least-upper-bound-family-of-elements-Poset z)
  is-prop-is-least-upper-bound-family-of-elements-Poset z =
    is-prop-type-Prop (is-least-upper-bound-family-of-elements-prop-Poset z)

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} {a : I → type-Poset P}
  where

  forward-implication-is-least-upper-bound-family-of-elements-Poset :
    {x y : type-Poset P} →
    is-least-upper-bound-family-of-elements-Poset P a x →
    is-upper-bound-family-of-elements-Poset P a y → leq-Poset P x y
  forward-implication-is-least-upper-bound-family-of-elements-Poset {x} {y} H =
    forward-implication (H y)

  backward-implication-is-least-upper-bound-family-of-elements-Poset :
    {x y : type-Poset P} →
    is-least-upper-bound-family-of-elements-Poset P a x →
    leq-Poset P x y → is-upper-bound-family-of-elements-Poset P a y
  backward-implication-is-least-upper-bound-family-of-elements-Poset {x} {y} H =
    backward-implication (H y)

  is-upper-bound-is-least-upper-bound-family-of-elements-Poset :
    {x : type-Poset P} →
    is-least-upper-bound-family-of-elements-Poset P a x →
    is-upper-bound-family-of-elements-Poset P a x
  is-upper-bound-is-least-upper-bound-family-of-elements-Poset {x} H =
    backward-implication-is-least-upper-bound-family-of-elements-Poset H
      ( refl-leq-Poset P x)
```

### The proposition that a family of elements has a least upper bound

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} (a : I → type-Poset P)
  where

  has-least-upper-bound-family-of-elements-Poset : UU (l1 ⊔ l2 ⊔ l3)
  has-least-upper-bound-family-of-elements-Poset =
    Σ (type-Poset P) (is-least-upper-bound-family-of-elements-Poset P a)

  all-elements-equal-has-least-upper-bound-family-of-elements-Poset :
    all-elements-equal has-least-upper-bound-family-of-elements-Poset
  all-elements-equal-has-least-upper-bound-family-of-elements-Poset
    ( x , H) (y , K) =
    eq-type-subtype
      ( is-least-upper-bound-family-of-elements-prop-Poset P a)
      ( antisymmetric-leq-Poset P x y
        ( forward-implication-is-least-upper-bound-family-of-elements-Poset
          ( P)
          ( H)
          ( is-upper-bound-is-least-upper-bound-family-of-elements-Poset
            ( P)
            ( K)))
        ( forward-implication-is-least-upper-bound-family-of-elements-Poset
          ( P)
          ( K)
          ( is-upper-bound-is-least-upper-bound-family-of-elements-Poset
            ( P)
            ( H))))

  is-prop-has-least-upper-bound-family-of-elements-Poset :
    is-prop has-least-upper-bound-family-of-elements-Poset
  is-prop-has-least-upper-bound-family-of-elements-Poset =
    is-prop-all-elements-equal
      all-elements-equal-has-least-upper-bound-family-of-elements-Poset

  has-least-upper-bound-family-of-elements-prop-Poset : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 has-least-upper-bound-family-of-elements-prop-Poset =
    has-least-upper-bound-family-of-elements-Poset
  pr2 has-least-upper-bound-family-of-elements-prop-Poset =
    is-prop-has-least-upper-bound-family-of-elements-Poset

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) {I : UU l3} {a : I → type-Poset P}
  where

  eq-is-least-upper-bound-family-of-elements-Poset :
    {x y : type-Poset P} →
    is-least-upper-bound-family-of-elements-Poset P a x →
    is-least-upper-bound-family-of-elements-Poset P a y →
    x ＝ y
  eq-is-least-upper-bound-family-of-elements-Poset {x} {y} H K =
    ap
      ( pr1)
      ( all-elements-equal-has-least-upper-bound-family-of-elements-Poset
        ( P)
        ( a)
        ( x , H)
        ( y , K))
```

## Properties

### Binary least upper bounds as least upper bounds of families

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b : type-Poset P)
  (H : has-least-binary-upper-bound-Poset P a b)
  where

  family-of-elements-has-least-binary-upper-bound-Poset :
    bool → type-Poset P
  family-of-elements-has-least-binary-upper-bound-Poset = rec-bool a b

  least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset :
    type-Poset P
  least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset =
    pr1 H

  is-least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset :
    is-least-upper-bound-family-of-elements-Poset P
      ( family-of-elements-has-least-binary-upper-bound-Poset)
      ( least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset)
  is-least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset x =
    ( λ f → pr1 (pr2 H x) (f true , f false)) ,
    ( λ u →
      ind-bool
        ( λ z →
          leq-Poset P
            ( family-of-elements-has-least-binary-upper-bound-Poset z)
            ( x))
        ( pr1 (pr2 (pr2 H x) u))
        ( pr2 (pr2 (pr2 H x) u)))

  has-least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset :
    has-least-upper-bound-family-of-elements-Poset P
      ( family-of-elements-has-least-binary-upper-bound-Poset)
  has-least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset =
    least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset ,
    is-least-upper-bound-family-of-elements-has-least-binary-upper-bound-Poset
```

### Least upper bounds of families over the booleans as binary least upper bounds

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (x : bool → type-Poset P)
  (H : has-least-upper-bound-family-of-elements-Poset P x)
  where

  least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset :
    type-Poset P
  least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset =
    pr1 H

  is-least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset :
    is-least-binary-upper-bound-Poset P
      ( x true)
      ( x false)
      ( least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset)
  is-least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset z =
    ( λ f →
      pr1 (pr2 H z) (ind-bool (λ i → leq-Poset P (x i) z) (pr1 f) (pr2 f))) ,
    ( λ u → pr2 (pr2 H z) u true , pr2 (pr2 H z) u false)

  has-least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset :
    has-least-binary-upper-bound-Poset P (x true) (x false)
  has-least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset =
    least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset ,
    is-least-binary-upper-bound-has-least-upper-bound-family-of-elements-Poset
```

### if $a ≤ b$ then $b$ is the least binary upper bound of $a$ and $b$

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2) (a b : type-Poset P) (p : leq-Poset P a b)
  where

  is-least-binary-upper-bound-leq-Poset :
    is-least-binary-upper-bound-Poset P a b b
  is-least-binary-upper-bound-leq-Poset x =
      ( λ f → pr2 f) ,
      ( λ f → transitive-leq-Poset P a b x f p , f)

  has-least-binary-upper-bound-leq-Poset :
    has-least-binary-upper-bound-Poset P a b
  has-least-binary-upper-bound-leq-Poset =
    ( b , is-least-binary-upper-bound-leq-Poset)
```
