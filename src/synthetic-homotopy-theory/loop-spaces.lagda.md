# Loop spaces

```agda
module synthetic-homotopy-theory.loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.wild-quasigroups
```

</details>

## Idea

The
{{#concept "loop space" Disambiguation="of a pointed type" Agda=Ω WD="loop space" WDID=Q2066070}}
of a [pointed type](structured-types.pointed-types.md) `A` is the pointed type
of self-[identifications](foundation-core.identity-types.md) of the base point
of `A`. The loop space comes equipped with a group-like structure induced by the
groupoidal-like structure on identifications.

## Table of files directly related to loop spaces

{{#include tables/loop-spaces-concepts.md}}

## Definitions

### The loop space of a pointed type

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Ω : UU l
  type-Ω = point-Pointed-Type A ＝ point-Pointed-Type A

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : Pointed-Type l
  Ω = (type-Ω , refl-Ω)
```

### The magma of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  mul-Ω : type-Ω A → type-Ω A → type-Ω A
  mul-Ω x y = x ∙ y

  Ω-Magma : Magma l
  pr1 Ω-Magma = type-Ω A
  pr2 Ω-Magma = mul-Ω
```

### The H-space of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  left-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω A (refl-Ω A) x ＝ x
  left-unit-law-mul-Ω x = left-unit

  right-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω A x (refl-Ω A) ＝ x
  right-unit-law-mul-Ω x = right-unit

  coherence-unit-laws-mul-Ω :
    left-unit-law-mul-Ω refl ＝ right-unit-law-mul-Ω refl
  coherence-unit-laws-mul-Ω = refl

  Ω-H-Space : H-Space l
  Ω-H-Space =
    ( Ω A ,
      mul-Ω A ,
      left-unit-law-mul-Ω ,
      right-unit-law-mul-Ω ,
      coherence-unit-laws-mul-Ω)
```

### The wild quasigroup of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  inv-Ω : type-Ω A → type-Ω A
  inv-Ω = inv

  left-inverse-law-mul-Ω :
    (x : type-Ω A) → mul-Ω A (inv-Ω x) x ＝ refl-Ω A
  left-inverse-law-mul-Ω x = left-inv x

  right-inverse-law-mul-Ω :
    (x : type-Ω A) → mul-Ω A x (inv-Ω x) ＝ refl-Ω A
  right-inverse-law-mul-Ω x = right-inv x

  Ω-Wild-Quasigroup : Wild-Quasigroup l
  pr1 Ω-Wild-Quasigroup = Ω-Magma A
  pr2 Ω-Wild-Quasigroup = is-binary-equiv-concat
```

### Associativity of concatenation on loop spaces

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  associative-mul-Ω :
    (x y z : type-Ω A) →
    mul-Ω A (mul-Ω A x y) z ＝ mul-Ω A x (mul-Ω A y z)
  associative-mul-Ω x y z = assoc x y z
```

We compute transport of `type-Ω`.

```agda
module _
  {l1 : Level} {A : UU l1} {x y : A}
  where

  equiv-tr-Ω : x ＝ y → Ω (A , x) ≃∗ Ω (A , y)
  equiv-tr-Ω refl = (id-equiv , refl)

  equiv-tr-type-Ω : x ＝ y → type-Ω (A , x) ≃ type-Ω (A , y)
  equiv-tr-type-Ω p =
    equiv-pointed-equiv (equiv-tr-Ω p)

  tr-type-Ω : x ＝ y → type-Ω (A , x) → type-Ω (A , y)
  tr-type-Ω p = map-equiv (equiv-tr-type-Ω p)

  is-equiv-tr-type-Ω : (p : x ＝ y) → is-equiv (tr-type-Ω p)
  is-equiv-tr-type-Ω p = is-equiv-map-equiv (equiv-tr-type-Ω p)

  preserves-refl-tr-Ω : (p : x ＝ y) → tr-type-Ω p refl ＝ refl
  preserves-refl-tr-Ω refl = refl

  preserves-mul-tr-Ω :
    (p : x ＝ y) (u v : type-Ω (A , x)) →
    tr-type-Ω p (mul-Ω (A , x) u v) ＝
    mul-Ω (A , y) (tr-type-Ω p u) (tr-type-Ω p v)
  preserves-mul-tr-Ω refl u v = refl

  preserves-inv-tr-Ω :
    (p : x ＝ y) (u : type-Ω (A , x)) →
    tr-type-Ω p (inv-Ω (A , x) u) ＝ inv-Ω (A , y) (tr-type-Ω p u)
  preserves-inv-tr-Ω refl u = refl

  eq-tr-type-Ω :
    (p : x ＝ y) (q : type-Ω (A , x)) →
    tr-type-Ω p q ＝ inv p ∙ (q ∙ p)
  eq-tr-type-Ω refl q = inv right-unit
```

## Properties

### Every pointed identity type is equivalent to a loop space

```agda
module _
  {l : Level} (A : Pointed-Type l) {x : type-Pointed-Type A}
  (p : point-Pointed-Type A ＝ x)
  where

  pointed-equiv-loop-pointed-identity :
    ( (point-Pointed-Type A ＝ x) , p) ≃∗ Ω A
  pointed-equiv-loop-pointed-identity =
    ( equiv-concat' (point-Pointed-Type A) (inv p) , right-inv p)
```

### The loop space of a (𝑘+1)-truncated type is 𝑘-truncated

```agda
module _
  {l : Level} (k : 𝕋) (A : Pointed-Type l)
  where

  is-trunc-Ω : is-trunc (succ-𝕋 k) (type-Pointed-Type A) → is-trunc k (type-Ω A)
  is-trunc-Ω H = H (point-Pointed-Type A) (point-Pointed-Type A)
```
