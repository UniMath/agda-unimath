# Normed real algebras

```agda
module linear-algebra.normed-real-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.lipschitz-continuity-scalar-multiplication-normed-real-vector-spaces
open import linear-algebra.lipschitz-maps-normed-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-algebras
open import linear-algebra.real-vector-spaces

open import logic.functoriality-existential-quantification

open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A {{#concept "normed real algebra" Agda=Normed-ℝ-Algebra}} is an
[algebra over ℝ](linear-algebra.real-algebras.md) `A` equipped with a
[norm](linear-algebra.normed-real-vector-spaces.md) with the property that for
any `x y : A`, the norm of `xy` is
[less than or equal to](real-numbers.inequality-real-numbers.md) the
[product](real-numbers.multiplication-real-numbers.md) of the norms of `x` and
`y`.

## Definition

```agda
is-submultiplicative-prop-norm-vector-space-ℝ-Algebra :
  {l1 l2 : Level} (A : ℝ-Algebra l1 l2) →
  subtype (l1 ⊔ l2) (norm-ℝ-Vector-Space (vector-space-ℝ-Algebra A))
is-submultiplicative-prop-norm-vector-space-ℝ-Algebra A n =
  Π-Prop
    ( type-ℝ-Algebra A)
    ( λ x →
      Π-Prop
        ( type-ℝ-Algebra A)
        ( λ y →
          let
            norm = map-norm-Normed-ℝ-Vector-Space (vector-space-ℝ-Algebra A , n)
          in
            leq-prop-ℝ (norm (mul-ℝ-Algebra A x y)) (norm x *ℝ norm y)))

norm-ℝ-Algebra : {l1 l2 : Level} → ℝ-Algebra l1 l2 → UU (lsuc l1 ⊔ l2)
norm-ℝ-Algebra A =
  type-subtype (is-submultiplicative-prop-norm-vector-space-ℝ-Algebra A)

Normed-ℝ-Algebra : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
Normed-ℝ-Algebra l1 l2 = Σ (ℝ-Algebra l1 l2) norm-ℝ-Algebra
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  where

  algebra-Normed-ℝ-Algebra : ℝ-Algebra l1 l2
  algebra-Normed-ℝ-Algebra = pr1 A

  vector-space-Normed-ℝ-Algebra : ℝ-Vector-Space l1 l2
  vector-space-Normed-ℝ-Algebra =
    vector-space-ℝ-Algebra algebra-Normed-ℝ-Algebra

  normed-vector-space-Normed-ℝ-Algebra : Normed-ℝ-Vector-Space l1 l2
  normed-vector-space-Normed-ℝ-Algebra =
    ( vector-space-Normed-ℝ-Algebra ,
      pr1 (pr2 A))

  ab-Normed-ℝ-Algebra : Ab l2
  ab-Normed-ℝ-Algebra = ab-ℝ-Vector-Space vector-space-Normed-ℝ-Algebra

  set-Normed-ℝ-Algebra : Set l2
  set-Normed-ℝ-Algebra = set-Ab ab-Normed-ℝ-Algebra

  type-Normed-ℝ-Algebra : UU l2
  type-Normed-ℝ-Algebra = type-Ab ab-Normed-ℝ-Algebra
```

## Properties

### Properties inherited by the Abelian group structure of addition

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (let ab-A = ab-Normed-ℝ-Algebra A)
  where

  add-Normed-ℝ-Algebra :
    type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A
  add-Normed-ℝ-Algebra = add-Ab ab-A

  zero-Normed-ℝ-Algebra : type-Normed-ℝ-Algebra A
  zero-Normed-ℝ-Algebra = zero-Ab ab-A

  diff-Normed-ℝ-Algebra :
    type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A
  diff-Normed-ℝ-Algebra = right-subtraction-Ab ab-A

  neg-Normed-ℝ-Algebra : type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A
  neg-Normed-ℝ-Algebra = neg-Ab ab-A

  abstract
    commutative-add-Normed-ℝ-Algebra :
      (x y : type-Normed-ℝ-Algebra A) →
      add-Normed-ℝ-Algebra x y ＝ add-Normed-ℝ-Algebra y x
    commutative-add-Normed-ℝ-Algebra = commutative-add-Ab ab-A

    distributive-neg-add-Normed-ℝ-Algebra :
      (x y : type-Normed-ℝ-Algebra A) →
      neg-Normed-ℝ-Algebra (add-Normed-ℝ-Algebra x y) ＝
      add-Normed-ℝ-Algebra (neg-Normed-ℝ-Algebra x) (neg-Normed-ℝ-Algebra y)
    distributive-neg-add-Normed-ℝ-Algebra = distributive-neg-add-Ab ab-A

    interchange-add-diff-Normed-ℝ-Algebra :
      (x y z w : type-Normed-ℝ-Algebra A) →
      diff-Normed-ℝ-Algebra
        ( add-Normed-ℝ-Algebra x y)
        ( add-Normed-ℝ-Algebra z w) ＝
      add-Normed-ℝ-Algebra
        ( diff-Normed-ℝ-Algebra x z)
        ( diff-Normed-ℝ-Algebra y w)
    interchange-add-diff-Normed-ℝ-Algebra =
      interchange-add-right-subtraction-Ab ab-A

    right-swap-add-Normed-ℝ-Algebra :
      (x y z : type-Normed-ℝ-Algebra A) →
      add-Normed-ℝ-Algebra (add-Normed-ℝ-Algebra x y) z ＝
      add-Normed-ℝ-Algebra (add-Normed-ℝ-Algebra x z) y
    right-swap-add-Normed-ℝ-Algebra = right-swap-add-Ab ab-A

    neg-diff-Normed-ℝ-Algebra :
      (x y : type-Normed-ℝ-Algebra A) →
      neg-Normed-ℝ-Algebra (diff-Normed-ℝ-Algebra x y) ＝
      diff-Normed-ℝ-Algebra y x
    neg-diff-Normed-ℝ-Algebra = neg-right-subtraction-Ab ab-A
```

### Properties inherited from the vector space structure

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (let vs-A = vector-space-Normed-ℝ-Algebra A)
  where

  scalar-mul-Normed-ℝ-Algebra :
    ℝ l1 → type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A
  scalar-mul-Normed-ℝ-Algebra = mul-ℝ-Vector-Space vs-A

  abstract
    left-distributive-scalar-mul-add-Normed-ℝ-Algebra :
      (c : ℝ l1) (x y : type-Normed-ℝ-Algebra A) →
      scalar-mul-Normed-ℝ-Algebra c (add-Normed-ℝ-Algebra A x y) ＝
      add-Normed-ℝ-Algebra A
        ( scalar-mul-Normed-ℝ-Algebra c x)
        ( scalar-mul-Normed-ℝ-Algebra c y)
    left-distributive-scalar-mul-add-Normed-ℝ-Algebra =
      left-distributive-mul-add-ℝ-Vector-Space vs-A
```

### Properties inherited from the algebra structure

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (let algebra-A = algebra-Normed-ℝ-Algebra A)
  where

  mul-Normed-ℝ-Algebra :
    type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A
  mul-Normed-ℝ-Algebra = mul-ℝ-Algebra algebra-A

  abstract
    left-distributive-mul-diff-Normed-ℝ-Algebra :
      (x y z : type-Normed-ℝ-Algebra A) →
      mul-Normed-ℝ-Algebra x (diff-Normed-ℝ-Algebra A y z) ＝
      diff-Normed-ℝ-Algebra A
        ( mul-Normed-ℝ-Algebra x y)
        ( mul-Normed-ℝ-Algebra x z)
    left-distributive-mul-diff-Normed-ℝ-Algebra =
      left-distributive-mul-diff-ℝ-Algebra algebra-A

    right-distributive-mul-add-Normed-ℝ-Algebra :
      (x y z : type-Normed-ℝ-Algebra A) →
      mul-Normed-ℝ-Algebra (add-Normed-ℝ-Algebra A x y) z ＝
      add-Normed-ℝ-Algebra A
        ( mul-Normed-ℝ-Algebra x z)
        ( mul-Normed-ℝ-Algebra y z)
    right-distributive-mul-add-Normed-ℝ-Algebra =
      right-distributive-mul-add-ℝ-Algebra algebra-A

    right-distributive-mul-diff-Normed-ℝ-Algebra :
      (x y z : type-Normed-ℝ-Algebra A) →
      mul-Normed-ℝ-Algebra (diff-Normed-ℝ-Algebra A x y) z ＝
      diff-Normed-ℝ-Algebra A
        ( mul-Normed-ℝ-Algebra x z)
        ( mul-Normed-ℝ-Algebra y z)
    right-distributive-mul-diff-Normed-ℝ-Algebra =
      right-distributive-mul-diff-ℝ-Algebra algebra-A

    left-negative-law-mul-Normed-ℝ-Algebra :
      (x y : type-Normed-ℝ-Algebra A) →
      mul-Normed-ℝ-Algebra (neg-Normed-ℝ-Algebra A x) y ＝
      neg-Normed-ℝ-Algebra A (mul-Normed-ℝ-Algebra x y)
    left-negative-law-mul-Normed-ℝ-Algebra =
      left-negative-law-mul-ℝ-Algebra algebra-A

    right-negative-law-mul-Normed-ℝ-Algebra :
      (x y : type-Normed-ℝ-Algebra A) →
      mul-Normed-ℝ-Algebra x (neg-Normed-ℝ-Algebra A y) ＝
      neg-Normed-ℝ-Algebra A (mul-Normed-ℝ-Algebra x y)
    right-negative-law-mul-Normed-ℝ-Algebra =
      right-negative-law-mul-ℝ-Algebra algebra-A

    left-swap-scalar-mul-mul-Normed-ℝ-Algebra :
      (c : ℝ l1) (x y : type-Normed-ℝ-Algebra A) →
      scalar-mul-Normed-ℝ-Algebra A c (mul-Normed-ℝ-Algebra x y) ＝
      mul-Normed-ℝ-Algebra x (scalar-mul-Normed-ℝ-Algebra A c y)
    left-swap-scalar-mul-mul-Normed-ℝ-Algebra =
      left-swap-scalar-mul-mul-ℝ-Algebra algebra-A

    associative-scalar-mul-mul-Normed-ℝ-Algebra :
      (c : ℝ l1) (x y : type-Normed-ℝ-Algebra A) →
      mul-Normed-ℝ-Algebra (scalar-mul-Normed-ℝ-Algebra A c x) y ＝
      scalar-mul-Normed-ℝ-Algebra A c (mul-Normed-ℝ-Algebra x y)
    associative-scalar-mul-mul-Normed-ℝ-Algebra =
      associative-scalar-mul-mul-ℝ-Algebra algebra-A
```

### Properties inherited from the normed real vector space structure

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (let normed-vector-space-A = normed-vector-space-Normed-ℝ-Algebra A)
  where

  map-norm-Normed-ℝ-Algebra : type-Normed-ℝ-Algebra A → ℝ l1
  map-norm-Normed-ℝ-Algebra =
    map-norm-Normed-ℝ-Vector-Space normed-vector-space-A

  nonnegative-norm-Normed-ℝ-Algebra : type-Normed-ℝ-Algebra A → ℝ⁰⁺ l1
  nonnegative-norm-Normed-ℝ-Algebra =
    nonnegative-norm-Normed-ℝ-Vector-Space normed-vector-space-A

  dist-Normed-ℝ-Algebra :
    type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A → ℝ l1
  dist-Normed-ℝ-Algebra =
    dist-Normed-ℝ-Vector-Space normed-vector-space-A

  nonnegative-dist-Normed-ℝ-Algebra :
    type-Normed-ℝ-Algebra A → type-Normed-ℝ-Algebra A → ℝ⁰⁺ l1
  nonnegative-dist-Normed-ℝ-Algebra =
    nonnegative-dist-Normed-ℝ-Vector-Space normed-vector-space-A

  metric-Normed-ℝ-Algebra : Metric l1 (set-Normed-ℝ-Algebra A)
  metric-Normed-ℝ-Algebra =
    metric-Normed-ℝ-Vector-Space normed-vector-space-A

  metric-space-Normed-ℝ-Algebra : Metric-Space l2 l1
  metric-space-Normed-ℝ-Algebra =
    metric-space-Normed-ℝ-Vector-Space normed-vector-space-A

  located-metric-space-Normed-ℝ-Algebra : Located-Metric-Space l2 l1
  located-metric-space-Normed-ℝ-Algebra =
    located-metric-space-Normed-ℝ-Vector-Space normed-vector-space-A

  abstract
    dist-left-add-Normed-ℝ-Algebra :
      (u v w : type-Normed-ℝ-Algebra A) →
      dist-Normed-ℝ-Algebra
        ( add-Normed-ℝ-Algebra A u v)
        ( add-Normed-ℝ-Algebra A u w) ＝
      dist-Normed-ℝ-Algebra v w
    dist-left-add-Normed-ℝ-Algebra =
      dist-left-add-Normed-ℝ-Vector-Space normed-vector-space-A

    dist-right-add-Normed-ℝ-Algebra :
      (u v w : type-Normed-ℝ-Algebra A) →
      dist-Normed-ℝ-Algebra
        ( add-Normed-ℝ-Algebra A v u)
        ( add-Normed-ℝ-Algebra A w u) ＝
      dist-Normed-ℝ-Algebra v w
    dist-right-add-Normed-ℝ-Algebra =
      dist-right-add-Normed-ℝ-Vector-Space normed-vector-space-A

    triangular-norm-Normed-ℝ-Algebra :
      (v w : type-Normed-ℝ-Algebra A) →
      leq-ℝ
        ( map-norm-Normed-ℝ-Algebra (add-Normed-ℝ-Algebra A v w))
        ( map-norm-Normed-ℝ-Algebra v +ℝ map-norm-Normed-ℝ-Algebra w)
    triangular-norm-Normed-ℝ-Algebra =
      triangular-norm-Normed-ℝ-Vector-Space normed-vector-space-A

    triangular-dist-Normed-ℝ-Algebra :
      (u v w : type-Normed-ℝ-Algebra A) →
      leq-ℝ
        ( dist-Normed-ℝ-Algebra u w)
        ( dist-Normed-ℝ-Algebra u v +ℝ dist-Normed-ℝ-Algebra v w)
    triangular-dist-Normed-ℝ-Algebra =
      triangular-dist-Normed-ℝ-Vector-Space normed-vector-space-A

    is-absolutely-homogeneous-norm-Normed-ℝ-Algebra :
      (c : ℝ l1) (v : type-Normed-ℝ-Algebra A) →
      map-norm-Normed-ℝ-Algebra (scalar-mul-Normed-ℝ-Algebra A c v) ＝
      abs-ℝ c *ℝ map-norm-Normed-ℝ-Algebra v
    is-absolutely-homogeneous-norm-Normed-ℝ-Algebra =
      is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space normed-vector-space-A
```

### Additional definitional properties of the normed real algebra

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  where

  is-submultiplicative-norm-Normed-ℝ-Algebra :
    (x y : type-Normed-ℝ-Algebra A) →
    leq-ℝ
      ( map-norm-Normed-ℝ-Algebra A (mul-Normed-ℝ-Algebra A x y))
      ( map-norm-Normed-ℝ-Algebra A x *ℝ
        map-norm-Normed-ℝ-Algebra A y)
  is-submultiplicative-norm-Normed-ℝ-Algebra = pr2 (pr2 A)
```

### Scalar multiplication by a constant is Lipschitz continuous

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (c : ℝ l1)
  where abstract

  is-lipschitz-left-scalar-mul-Normed-ℝ-Algebra :
    is-lipschitz-map-Metric-Space
      ( metric-space-Normed-ℝ-Algebra A)
      ( metric-space-Normed-ℝ-Algebra A)
      ( scalar-mul-Normed-ℝ-Algebra A c)
  is-lipschitz-left-scalar-mul-Normed-ℝ-Algebra =
    is-lipschitz-left-mul-Normed-ℝ-Vector-Space
      ( normed-vector-space-Normed-ℝ-Algebra A)
      ( c)
```

### Left multiplication by a constant is Lipschitz continuous

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (x : type-Normed-ℝ-Algebra A)
  (let algebra-A = algebra-Normed-ℝ-Algebra A)
  (let normed-vector-space-A = normed-vector-space-Normed-ℝ-Algebra A)
  where abstract

  is-lipschitz-left-mul-Normed-ℝ-Algebra :
    is-lipschitz-map-Metric-Space
      ( metric-space-Normed-ℝ-Algebra A)
      ( metric-space-Normed-ℝ-Algebra A)
      ( mul-Normed-ℝ-Algebra A x)
  is-lipschitz-left-mul-Normed-ℝ-Algebra =
    let
      norm-A = map-norm-Normed-ℝ-Algebra A
      dist-A = dist-Normed-ℝ-Algebra A
      _*A_ = mul-Normed-ℝ-Algebra A
      _-A_ = diff-Normed-ℝ-Algebra A
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      is-lipschitz-real-constant-map-Normed-ℝ-Vector-Space
        ( normed-vector-space-A)
        ( normed-vector-space-A)
        ( mul-Normed-ℝ-Algebra A x)
        ( nonnegative-norm-Normed-ℝ-Algebra A x)
        ( λ y z →
          chain-of-inequalities
            dist-A (x *A y) (x *A z)
            ≤ norm-A (x *A (y -A z))
              by
                leq-eq-ℝ
                  ( ap
                    ( norm-A)
                    ( inv
                      ( left-distributive-mul-diff-Normed-ℝ-Algebra A x y z)))
            ≤ norm-A x *ℝ dist-A y z
              by is-submultiplicative-norm-Normed-ℝ-Algebra A _ _)
```

### Right multiplication by a constant is Lipschitz continuous

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  (y : type-Normed-ℝ-Algebra A)
  (let algebra-A = algebra-Normed-ℝ-Algebra A)
  (let normed-vector-space-A = normed-vector-space-Normed-ℝ-Algebra A)
  where abstract

  is-lipschitz-right-mul-Normed-ℝ-Algebra :
    is-lipschitz-map-Metric-Space
      ( metric-space-Normed-ℝ-Algebra A)
      ( metric-space-Normed-ℝ-Algebra A)
      ( λ x → mul-Normed-ℝ-Algebra A x y)
  is-lipschitz-right-mul-Normed-ℝ-Algebra =
    let
      norm-A = map-norm-Normed-ℝ-Algebra A
      dist-A = dist-Normed-ℝ-Algebra A
      _*A_ = mul-Normed-ℝ-Algebra A
      _-A_ = diff-Normed-ℝ-Algebra A
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      is-lipschitz-real-constant-map-Normed-ℝ-Vector-Space
        ( normed-vector-space-A)
        ( normed-vector-space-A)
        ( λ x → mul-Normed-ℝ-Algebra A x y)
        ( nonnegative-norm-Normed-ℝ-Algebra A y)
        ( λ x1 x2 →
          chain-of-inequalities
            dist-A (x1 *A y) (x2 *A y)
            ≤ norm-A ((x1 -A x2) *A y)
              by
                leq-eq-ℝ
                  ( ap
                    ( norm-A)
                    ( inv
                      ( right-distributive-mul-diff-Normed-ℝ-Algebra A
                        ( x1)
                        ( x2)
                        ( y))))
            ≤ dist-A x1 x2 *ℝ norm-A y
              by is-submultiplicative-norm-Normed-ℝ-Algebra A _ _
            ≤ norm-A y *ℝ dist-A x1 x2
              by leq-eq-ℝ (commutative-mul-ℝ _ _))
```

### Submultiplicativity of distances

```agda
module _
  {l1 l2 : Level}
  (A : Normed-ℝ-Algebra l1 l2)
  where abstract

  leq-dist-left-mul-Normed-ℝ-Algebra :
    (x y z : type-Normed-ℝ-Algebra A) →
    leq-ℝ
      ( dist-Normed-ℝ-Algebra A
        ( mul-Normed-ℝ-Algebra A x y)
        ( mul-Normed-ℝ-Algebra A x z))
      ( map-norm-Normed-ℝ-Algebra A x *ℝ dist-Normed-ℝ-Algebra A y z)
  leq-dist-left-mul-Normed-ℝ-Algebra x y z =
    tr
      ( λ w →
        leq-ℝ
          ( map-norm-Normed-ℝ-Algebra A w)
          ( map-norm-Normed-ℝ-Algebra A x *ℝ dist-Normed-ℝ-Algebra A y z))
      ( left-distributive-mul-diff-Normed-ℝ-Algebra A x y z)
      ( is-submultiplicative-norm-Normed-ℝ-Algebra A _ _)

  leq-dist-right-mul-Normed-ℝ-Algebra :
    (x y z : type-Normed-ℝ-Algebra A) →
    leq-ℝ
      ( dist-Normed-ℝ-Algebra A
        ( mul-Normed-ℝ-Algebra A x z)
        ( mul-Normed-ℝ-Algebra A y z))
      ( dist-Normed-ℝ-Algebra A x y *ℝ map-norm-Normed-ℝ-Algebra A z)
  leq-dist-right-mul-Normed-ℝ-Algebra x y z =
    tr
      ( λ w →
        leq-ℝ
          ( map-norm-Normed-ℝ-Algebra A w)
          ( dist-Normed-ℝ-Algebra A x y *ℝ map-norm-Normed-ℝ-Algebra A z))
      ( right-distributive-mul-diff-Normed-ℝ-Algebra A x y z)
      ( is-submultiplicative-norm-Normed-ℝ-Algebra A _ _)
```
