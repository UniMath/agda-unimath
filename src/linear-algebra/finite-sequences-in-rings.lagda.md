# Finite sequences in rings

```agda
module linear-algebra.finite-sequences-in-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-semirings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import ring-theory.function-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

For any [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`,
and [ring](ring-theory.rings.md) `R`, the
{{#concept "left module of finite sequences" Disambiguation="in a ring" Agda=left-module-fin-sequence-Ring}}
of length `n` in `R` is the
`R`-[left-module](linear-algebra.left-modules-rings.md) of
[functions](ring-theory.function-rings.md) `Fin n → R`.

## Definitions

### The ring of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ)
  where

  ring-fin-sequence-Ring : Ring l
  ring-fin-sequence-Ring =
    function-Ring R (Fin n)
```

### The left module of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ)
  where

  left-module-fin-sequence-Ring : left-module-Ring l R
  left-module-fin-sequence-Ring =
    left-module-function-Ring R (Fin n)

  fin-sequence-type-Ring : UU l
  fin-sequence-type-Ring = fin-sequence (type-Ring R) n
```

### The abelian group of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ)
  where

  ab-fin-sequence-type-Ring : Ab l
  ab-fin-sequence-type-Ring =
    ab-left-module-Ring R (left-module-fin-sequence-Ring R n)
```

### Constructors and accessors for finite sequences in rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  head-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring R (succ-ℕ n) → type-Ring R
  head-fin-sequence-type-Ring n v = head-fin-sequence n v

  tail-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring R (succ-ℕ n) → fin-sequence-type-Ring R n
  tail-fin-sequence-type-Ring = tail-fin-sequence

  cons-fin-sequence-type-Ring :
    (n : ℕ) → type-Ring R →
    fin-sequence-type-Ring R n → fin-sequence-type-Ring R (succ-ℕ n)
  cons-fin-sequence-type-Ring = cons-fin-sequence

  snoc-fin-sequence-type-Ring :
    (n : ℕ) → fin-sequence-type-Ring R n → type-Ring R →
    fin-sequence-type-Ring R (succ-ℕ n)
  snoc-fin-sequence-type-Ring = snoc-fin-sequence
```

### The zero finite sequence in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  zero-fin-sequence-type-Ring : (n : ℕ) → fin-sequence-type-Ring R n
  zero-fin-sequence-type-Ring = zero-Ring ∘ function-Ring R ∘ Fin
```

### Pointwise addition of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-fin-sequence-type-Ring :
    (n : ℕ) (v w : fin-sequence-type-Ring R n) → fin-sequence-type-Ring R n
  add-fin-sequence-type-Ring = add-Ring ∘ function-Ring R ∘ Fin
```

### Pointwise negation of finite sequences in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) → fin-sequence-type-Ring R n
  neg-fin-sequence-type-Ring = neg-Ring ∘ function-Ring R ∘ Fin
```

## Properties of pointwise addition

### Associativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  associative-add-fin-sequence-type-Ring :
    (n : ℕ) (v1 v2 v3 : fin-sequence-type-Ring R n) →
    ( add-fin-sequence-type-Ring R n
      ( add-fin-sequence-type-Ring R n v1 v2)
      ( v3)) ＝
    ( add-fin-sequence-type-Ring R n v1 (add-fin-sequence-type-Ring R n v2 v3))
  associative-add-fin-sequence-type-Ring =
    associative-add-Ring ∘ function-Ring R ∘ Fin
```

### Unit laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-unit-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n (zero-fin-sequence-type-Ring R n) v ＝ v
  left-unit-law-add-fin-sequence-type-Ring =
    left-unit-law-add-Ring ∘ function-Ring R ∘ Fin

  right-unit-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v (zero-fin-sequence-type-Ring R n) ＝ v
  right-unit-law-add-fin-sequence-type-Ring =
    right-unit-law-add-Ring ∘ function-Ring R ∘ Fin
```

### Commutativity

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-add-fin-sequence-type-Ring :
    (n : ℕ) (v w : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v w ＝ add-fin-sequence-type-Ring R n w v
  commutative-add-fin-sequence-type-Ring =
    commutative-add-Ring ∘ function-Ring R ∘ Fin
```

### Inverse laws

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-inverse-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n (neg-fin-sequence-type-Ring R n v) v ＝
    zero-fin-sequence-type-Ring R n
  left-inverse-law-add-fin-sequence-type-Ring =
    left-inverse-law-add-Ring ∘ function-Ring R ∘ Fin

  right-inverse-law-add-fin-sequence-type-Ring :
    (n : ℕ) (v : fin-sequence-type-Ring R n) →
    add-fin-sequence-type-Ring R n v (neg-fin-sequence-type-Ring R n v) ＝
    zero-fin-sequence-type-Ring R n
  right-inverse-law-add-fin-sequence-type-Ring =
    right-inverse-law-add-Ring ∘ function-Ring R ∘ Fin
```

### The coordinate homomorphisms

```agda
module _
  {l : Level} (R : Ring l) (n : ℕ) (i : Fin n)
  where

  coordinate-hom-ring-fin-sequence-Ring :
    hom-Ring (ring-fin-sequence-Ring R n) R
  coordinate-hom-ring-fin-sequence-Ring =
    ev-hom-function-Ring R (Fin n) i

  coordinate-map-fin-sequence-Ring :
    fin-sequence-type-Ring R n → type-Ring R
  coordinate-map-fin-sequence-Ring =
    map-hom-Ring
      ( ring-fin-sequence-Ring R n)
      ( R)
      ( coordinate-hom-ring-fin-sequence-Ring)

  preserves-add-coordinate-map-fin-sequence-Ring :
    is-additive-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
      ( coordinate-map-fin-sequence-Ring)
  preserves-add-coordinate-map-fin-sequence-Ring x y =
    preserves-add-hom-Ring
      ( ring-fin-sequence-Ring R n)
      ( R)
      ( coordinate-hom-ring-fin-sequence-Ring)
      { x}
      { y}

  is-homogeneous-coordinate-map-fin-sequence-Ring :
    is-homogeneous-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
      ( coordinate-map-fin-sequence-Ring)
  is-homogeneous-coordinate-map-fin-sequence-Ring c x = refl

  is-linear-coordinate-map-fin-sequence-Ring :
    is-linear-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
      ( coordinate-map-fin-sequence-Ring)
  is-linear-coordinate-map-fin-sequence-Ring =
    preserves-add-coordinate-map-fin-sequence-Ring ,
    is-homogeneous-coordinate-map-fin-sequence-Ring

  coordinate-linear-map-fin-sequence-Ring :
    linear-map-left-module-Ring
      ( R)
      ( left-module-fin-sequence-Ring R n)
      ( left-module-ring-Ring R)
  coordinate-linear-map-fin-sequence-Ring =
    coordinate-map-fin-sequence-Ring ,
    is-linear-coordinate-map-fin-sequence-Ring
```
