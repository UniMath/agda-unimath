# Vectors on euclidean domains

```agda
open import foundation.function-extensionality-axiom

module
  linear-algebra.vectors-on-euclidean-domains
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.euclidean-domains funext

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext

open import foundation.identity-types funext
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.commutative-monoids funext
open import group-theory.groups funext
open import group-theory.monoids funext
open import group-theory.semigroups funext

open import linear-algebra.constant-vectors funext
open import linear-algebra.functoriality-vectors funext
open import linear-algebra.vectors funext
```

</details>

## Idea

Given an euclidean domain `R`, the type `vec n R` of `R`-vectors is an
`R`-module.

## Definitions

### Listed vectors on euclidean domains

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  vec-Euclidean-Domain : ℕ → UU l
  vec-Euclidean-Domain = vec (type-Euclidean-Domain R)

  head-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain (succ-ℕ n) → type-Euclidean-Domain R
  head-vec-Euclidean-Domain v = head-vec v

  tail-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain (succ-ℕ n) → vec-Euclidean-Domain n
  tail-vec-Euclidean-Domain v = tail-vec v

  snoc-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain n →
    type-Euclidean-Domain R → vec-Euclidean-Domain (succ-ℕ n)
  snoc-vec-Euclidean-Domain v r = snoc-vec v r
```

### Functional vectors on euclidean domains

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  functional-vec-Euclidean-Domain : ℕ → UU l
  functional-vec-Euclidean-Domain = functional-vec (type-Euclidean-Domain R)

  head-functional-vec-Euclidean-Domain :
    (n : ℕ) →
    functional-vec-Euclidean-Domain (succ-ℕ n) →
    type-Euclidean-Domain R
  head-functional-vec-Euclidean-Domain n v = head-functional-vec n v

  tail-functional-vec-Euclidean-Domain :
    (n : ℕ) →
    functional-vec-Euclidean-Domain (succ-ℕ n) →
    functional-vec-Euclidean-Domain n
  tail-functional-vec-Euclidean-Domain = tail-functional-vec

  cons-functional-vec-Euclidean-Domain :
    (n : ℕ) → type-Euclidean-Domain R →
    functional-vec-Euclidean-Domain n →
    functional-vec-Euclidean-Domain (succ-ℕ n)
  cons-functional-vec-Euclidean-Domain = cons-functional-vec

  snoc-functional-vec-Euclidean-Domain :
    (n : ℕ) → functional-vec-Euclidean-Domain n → type-Euclidean-Domain R →
    functional-vec-Euclidean-Domain (succ-ℕ n)
  snoc-functional-vec-Euclidean-Domain = snoc-functional-vec
```

### Zero vector on a euclidean domain

#### The zero listed vector

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-vec-Euclidean-Domain : {n : ℕ} → vec-Euclidean-Domain R n
  zero-vec-Euclidean-Domain = constant-vec (zero-Euclidean-Domain R)
```

#### The zero functional vector

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  zero-functional-vec-Euclidean-Domain :
    (n : ℕ) → functional-vec-Euclidean-Domain R n
  zero-functional-vec-Euclidean-Domain n i = zero-Euclidean-Domain R
```

### Pointwise addition of vectors on a euclidean domain

#### Pointwise addition of listed vectors on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-vec-Euclidean-Domain :
    {n : ℕ} →
    vec-Euclidean-Domain R n →
    vec-Euclidean-Domain R n →
    vec-Euclidean-Domain R n
  add-vec-Euclidean-Domain = binary-map-vec (add-Euclidean-Domain R)

  associative-add-vec-Euclidean-Domain :
    {n : ℕ} (v1 v2 v3 : vec-Euclidean-Domain R n) →
    Id
      ( add-vec-Euclidean-Domain (add-vec-Euclidean-Domain v1 v2) v3)
      ( add-vec-Euclidean-Domain v1 (add-vec-Euclidean-Domain v2 v3))
  associative-add-vec-Euclidean-Domain empty-vec empty-vec empty-vec = refl
  associative-add-vec-Euclidean-Domain (x ∷ v1) (y ∷ v2) (z ∷ v3) =
    ap-binary _∷_
      ( associative-add-Euclidean-Domain R x y z)
      ( associative-add-vec-Euclidean-Domain v1 v2 v3)

  vec-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  pr1 (vec-Euclidean-Domain-Semigroup n) = vec-Set (set-Euclidean-Domain R) n
  pr1 (pr2 (vec-Euclidean-Domain-Semigroup n)) = add-vec-Euclidean-Domain
  pr2 (pr2 (vec-Euclidean-Domain-Semigroup n)) =
    associative-add-vec-Euclidean-Domain

  left-unit-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id (add-vec-Euclidean-Domain (zero-vec-Euclidean-Domain R) v) v
  left-unit-law-add-vec-Euclidean-Domain empty-vec = refl
  left-unit-law-add-vec-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-add-Euclidean-Domain R x)
      ( left-unit-law-add-vec-Euclidean-Domain v)

  right-unit-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id (add-vec-Euclidean-Domain v (zero-vec-Euclidean-Domain R)) v
  right-unit-law-add-vec-Euclidean-Domain empty-vec = refl
  right-unit-law-add-vec-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( right-unit-law-add-Euclidean-Domain R x)
      ( right-unit-law-add-vec-Euclidean-Domain v)

  vec-Euclidean-Domain-Monoid : ℕ → Monoid l
  pr1 (vec-Euclidean-Domain-Monoid n) = vec-Euclidean-Domain-Semigroup n
  pr1 (pr2 (vec-Euclidean-Domain-Monoid n)) = zero-vec-Euclidean-Domain R
  pr1 (pr2 (pr2 (vec-Euclidean-Domain-Monoid n))) =
    left-unit-law-add-vec-Euclidean-Domain
  pr2 (pr2 (pr2 (vec-Euclidean-Domain-Monoid n))) =
    right-unit-law-add-vec-Euclidean-Domain

  commutative-add-vec-Euclidean-Domain :
    {n : ℕ} (v w : vec-Euclidean-Domain R n) →
    Id (add-vec-Euclidean-Domain v w) (add-vec-Euclidean-Domain w v)
  commutative-add-vec-Euclidean-Domain empty-vec empty-vec = refl
  commutative-add-vec-Euclidean-Domain (x ∷ v) (y ∷ w) =
    ap-binary _∷_
      ( commutative-add-Euclidean-Domain R x y)
      ( commutative-add-vec-Euclidean-Domain v w)

  vec-Euclidean-Domain-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (vec-Euclidean-Domain-Commutative-Monoid n) =
    vec-Euclidean-Domain-Monoid n
  pr2 (vec-Euclidean-Domain-Commutative-Monoid n) =
    commutative-add-vec-Euclidean-Domain
```

#### Pointwise addition of functional vectors on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v w : functional-vec-Euclidean-Domain R n) →
    functional-vec-Euclidean-Domain R n
  add-functional-vec-Euclidean-Domain n =
    binary-map-functional-vec n (add-Euclidean-Domain R)

  associative-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v1 v2 v3 : functional-vec-Euclidean-Domain R n) →
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( add-functional-vec-Euclidean-Domain n v1 v2)
      ( v3)) ＝
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( v1)
      ( add-functional-vec-Euclidean-Domain n v2 v3))
  associative-add-functional-vec-Euclidean-Domain n v1 v2 v3 =
    eq-htpy (λ i → associative-add-Euclidean-Domain R (v1 i) (v2 i) (v3 i))

  functional-vec-Euclidean-Domain-Semigroup : ℕ → Semigroup l
  pr1 (functional-vec-Euclidean-Domain-Semigroup n) =
    functional-vec-Set (set-Euclidean-Domain R) n
  pr1 (pr2 (functional-vec-Euclidean-Domain-Semigroup n)) =
    add-functional-vec-Euclidean-Domain n
  pr2 (pr2 (functional-vec-Euclidean-Domain-Semigroup n)) =
    associative-add-functional-vec-Euclidean-Domain n

  left-unit-law-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v : functional-vec-Euclidean-Domain R n) →
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( zero-functional-vec-Euclidean-Domain R n)
      ( v)) ＝
    ( v)
  left-unit-law-add-functional-vec-Euclidean-Domain n v =
    eq-htpy (λ i → left-unit-law-add-Euclidean-Domain R (v i))

  right-unit-law-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v : functional-vec-Euclidean-Domain R n) →
    ( add-functional-vec-Euclidean-Domain
      ( n)
      ( v)
      ( zero-functional-vec-Euclidean-Domain R n)) ＝
    ( v)
  right-unit-law-add-functional-vec-Euclidean-Domain n v =
    eq-htpy (λ i → right-unit-law-add-Euclidean-Domain R (v i))

  functional-vec-Euclidean-Domain-Monoid : ℕ → Monoid l
  pr1 (functional-vec-Euclidean-Domain-Monoid n) =
    functional-vec-Euclidean-Domain-Semigroup n
  pr1 (pr2 (functional-vec-Euclidean-Domain-Monoid n)) =
    zero-functional-vec-Euclidean-Domain R n
  pr1 (pr2 (pr2 (functional-vec-Euclidean-Domain-Monoid n))) =
    left-unit-law-add-functional-vec-Euclidean-Domain n
  pr2 (pr2 (pr2 (functional-vec-Euclidean-Domain-Monoid n))) =
    right-unit-law-add-functional-vec-Euclidean-Domain n

  commutative-add-functional-vec-Euclidean-Domain :
    (n : ℕ) (v w : functional-vec-Euclidean-Domain R n) →
    add-functional-vec-Euclidean-Domain n v w ＝
    add-functional-vec-Euclidean-Domain n w v
  commutative-add-functional-vec-Euclidean-Domain n v w =
    eq-htpy (λ i → commutative-add-Euclidean-Domain R (v i) (w i))

  functional-vec-Euclidean-Domain-Commutative-Monoid : ℕ → Commutative-Monoid l
  pr1 (functional-vec-Euclidean-Domain-Commutative-Monoid n) =
    functional-vec-Euclidean-Domain-Monoid n
  pr2 (functional-vec-Euclidean-Domain-Commutative-Monoid n) =
    commutative-add-functional-vec-Euclidean-Domain n
```

### The negative of a vector on a euclidean domain

```agda
module _
  {l : Level} (R : Euclidean-Domain l)
  where

  neg-vec-Euclidean-Domain :
    {n : ℕ} → vec-Euclidean-Domain R n → vec-Euclidean-Domain R n
  neg-vec-Euclidean-Domain = map-vec (neg-Euclidean-Domain R)

  left-inverse-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id
      ( add-vec-Euclidean-Domain R (neg-vec-Euclidean-Domain v) v)
      ( zero-vec-Euclidean-Domain R)
  left-inverse-law-add-vec-Euclidean-Domain empty-vec = refl
  left-inverse-law-add-vec-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( left-inverse-law-add-Euclidean-Domain R x)
      ( left-inverse-law-add-vec-Euclidean-Domain v)

  right-inverse-law-add-vec-Euclidean-Domain :
    {n : ℕ} (v : vec-Euclidean-Domain R n) →
    Id
      ( add-vec-Euclidean-Domain R v (neg-vec-Euclidean-Domain v))
      ( zero-vec-Euclidean-Domain R)
  right-inverse-law-add-vec-Euclidean-Domain empty-vec = refl
  right-inverse-law-add-vec-Euclidean-Domain (x ∷ v) =
    ap-binary _∷_
      ( right-inverse-law-add-Euclidean-Domain R x)
      ( right-inverse-law-add-vec-Euclidean-Domain v)

  is-unital-vec-Euclidean-Domain :
    (n : ℕ) → is-unital (add-vec-Euclidean-Domain R {n})
  pr1 (is-unital-vec-Euclidean-Domain n) = zero-vec-Euclidean-Domain R
  pr1 (pr2 (is-unital-vec-Euclidean-Domain n)) =
    left-unit-law-add-vec-Euclidean-Domain R
  pr2 (pr2 (is-unital-vec-Euclidean-Domain n)) =
    right-unit-law-add-vec-Euclidean-Domain R

  is-group-vec-Euclidean-Domain :
    (n : ℕ) → is-group-Semigroup (vec-Euclidean-Domain-Semigroup R n)
  pr1 (is-group-vec-Euclidean-Domain n) = is-unital-vec-Euclidean-Domain n
  pr1 (pr2 (is-group-vec-Euclidean-Domain n)) = neg-vec-Euclidean-Domain
  pr1 (pr2 (pr2 (is-group-vec-Euclidean-Domain n))) =
    left-inverse-law-add-vec-Euclidean-Domain
  pr2 (pr2 (pr2 (is-group-vec-Euclidean-Domain n))) =
    right-inverse-law-add-vec-Euclidean-Domain

  vec-Euclidean-Domain-Group : ℕ → Group l
  pr1 (vec-Euclidean-Domain-Group n) = vec-Euclidean-Domain-Semigroup R n
  pr2 (vec-Euclidean-Domain-Group n) = is-group-vec-Euclidean-Domain n

  vec-Euclidean-Domain-Ab : ℕ → Ab l
  pr1 (vec-Euclidean-Domain-Ab n) = vec-Euclidean-Domain-Group n
  pr2 (vec-Euclidean-Domain-Ab n) = commutative-add-vec-Euclidean-Domain R
```
