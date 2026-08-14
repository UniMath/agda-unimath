# Linear combinations with respect to commutative semirings

```agda
module
  commutative-algebra.linear-combinations-of-elements-commutative-semirings
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.monoids-with-commutative-semiring-action
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels-unit-type
open import foundation.sets
open import foundation.singleton-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.monoids

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists

open import ring-theory.linear-combinations-of-elements-semirings

open import structured-types.magmas
```

</details>

## Idea

Consider a [commutative semiring](commutative-algebra.commutative-semirings.md) $R$ and a type $A$. A {#concept "linear combination"}} of elements of $A$ is a [list](lists.lists.md) of pairs $(r,a,s)$ consisting of an element $r,s:R$ and an element $a:A$.

Furthermore, if we are given an action $\mu : R \to A \to R \to M$ taking values in a [unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate a linear combination $((r_0,a_0,s_0),\ldots,(r_{n-1},a_{n-1},s_{n-1}))$ by defining

$$
  ev((r_0,a_0,s_0),\ldots,(r_{n-1},a_{n-1},s_{n-1})) :=
  \sum_{i=0}^{n-1} \mu(r_i,a_i,s_i).
$$

To be explicit, linear combinations of elements of a type $A$ have the commutative semiring coefficients on both sides.

## Definitions

### The type of linear combinations

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : UU l2)
  where

  linear-combination-Commutative-Semiring :
    UU (l1 ⊔ l2)
  linear-combination-Commutative-Semiring =
    linear-combination-Semiring (semiring-Commutative-Semiring R) A
```

### Multiplying linear combinations by a scalar from the left, from the right, and from both sides

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) {A : UU l2}
  where

  left-mul-linear-combination-Commutative-Semiring :
    type-Commutative-Semiring R →
    linear-combination-Commutative-Semiring R A →
    linear-combination-Commutative-Semiring R A
  left-mul-linear-combination-Commutative-Semiring =
    left-mul-linear-combination-Semiring (semiring-Commutative-Semiring R)

  right-mul-linear-combination-Commutative-Semiring :
    linear-combination-Commutative-Semiring R A →
    type-Commutative-Semiring R →
    linear-combination-Commutative-Semiring R A
  right-mul-linear-combination-Commutative-Semiring =
    right-mul-linear-combination-Semiring (semiring-Commutative-Semiring R)

  mul-linear-combination-Commutative-Semiring :
    type-Commutative-Semiring R →
    linear-combination-Commutative-Semiring R A →
    type-Commutative-Semiring R →
    linear-combination-Commutative-Semiring R A
  mul-linear-combination-Commutative-Semiring =
    mul-linear-combination-Semiring (semiring-Commutative-Semiring R)
```

### Evaluating linear combinations of elements

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  {A : UU l2}
  where

  ev-unital-magma-linear-combination-Commutative-Semiring :
    (M : Unital-Magma l3)
    (μ :
      type-Commutative-Semiring R → A →
      type-Commutative-Semiring R → type-Unital-Magma M) →
    linear-combination-Commutative-Semiring R A → type-Unital-Magma M
  ev-unital-magma-linear-combination-Commutative-Semiring =
    ev-unital-magma-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)

  ev-monoid-linear-combination-Commutative-Semiring :
    (M : Monoid l3)
    (μ :
      type-Commutative-Semiring R → A →
      type-Commutative-Semiring R → type-Monoid M) →
    linear-combination-Commutative-Semiring R A → type-Monoid M
  ev-monoid-linear-combination-Commutative-Semiring =
    ev-monoid-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
```

### The predicate of being a linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  {A : UU l2}
  where

  is-linear-combination-Commutative-Semiring :
    (M : Unital-Magma l3)
    (μ :
      type-Commutative-Semiring R → A →
      type-Commutative-Semiring R → type-Unital-Magma M) →
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-linear-combination-Commutative-Semiring =
    is-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)

  is-linear-combination-monoid-Commutative-Semiring :
    (M : Monoid l3)
    (μ :
      type-Commutative-Semiring R → A →
      type-Commutative-Semiring R → type-Monoid M) →
    type-Monoid M → UU (l1 ⊔ l2 ⊔ l3)
  is-linear-combination-monoid-Commutative-Semiring =
    is-linear-combination-monoid-Semiring
      ( semiring-Commutative-Semiring R)
```

### The predicate of being a mere linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ :
    type-Commutative-Semiring R → A →
    type-Commutative-Semiring R → type-Unital-Magma M)
  where

  is-mere-linear-combination-prop-Commutative-Semiring :
    type-Unital-Magma M → Prop (l1 ⊔ l2 ⊔ l3)
  is-mere-linear-combination-prop-Commutative-Semiring =
    is-mere-linear-combination-prop-Semiring
      ( semiring-Commutative-Semiring R)
      ( M)
      ( μ)

  is-mere-linear-combination-Commutative-Semiring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-mere-linear-combination-Commutative-Semiring =
    is-mere-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( M)
      ( μ)

  is-prop-is-mere-linear-combination-Commutative-Semiring :
    (x : type-Unital-Magma M) →
    is-prop (is-mere-linear-combination-Commutative-Semiring x)
  is-prop-is-mere-linear-combination-Commutative-Semiring =
    is-prop-is-mere-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( M)
      ( μ)
```

### Linear combinations of elements of subsets of a commutative semiring

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 R)
  where

  linear-combination-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  linear-combination-subset-Commutative-Semiring =
    linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  two-sided-scalar-multiplication-subset-Commutative-Semiring :
    type-Commutative-Semiring R →
    type-subset-Commutative-Semiring R S →
    type-Commutative-Semiring R →
    type-Commutative-Semiring R
  two-sided-scalar-multiplication-subset-Commutative-Semiring =
    two-sided-scalar-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  ev-linear-combination-subset-Commutative-Semiring :
    linear-combination-subset-Commutative-Semiring → type-Commutative-Semiring R
  ev-linear-combination-subset-Commutative-Semiring =
    ev-linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  is-linear-combination-subset-Commutative-Semiring :
    type-Commutative-Semiring R → UU (l1 ⊔ l2)
  is-linear-combination-subset-Commutative-Semiring =
    is-linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  is-mere-linear-combination-prop-subset-Commutative-Semiring :
    type-Commutative-Semiring R → Prop (l1 ⊔ l2)
  is-mere-linear-combination-prop-subset-Commutative-Semiring =
    is-mere-linear-combination-prop-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  is-mere-linear-combination-subset-Commutative-Semiring :
    type-Commutative-Semiring R → UU (l1 ⊔ l2)
  is-mere-linear-combination-subset-Commutative-Semiring  =
    is-mere-linear-combination-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)
```

### Linear combinations of families of elements in a commutative semiring

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) {I : UU l2} (a : I → type-Commutative-Semiring R)
  where

  linear-combination-family-of-elements-Commutative-Semiring :
    UU (l1 ⊔ l2)
  linear-combination-family-of-elements-Commutative-Semiring =
    linear-combination-family-of-elements-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)

  ev-linear-combination-family-of-elements-Commutative-Semiring :
    linear-combination-family-of-elements-Commutative-Semiring →
    type-Commutative-Semiring R
  ev-linear-combination-family-of-elements-Commutative-Semiring =
    ev-linear-combination-family-of-elements-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)

  is-linear-combination-family-of-elements-Commutative-Semiring :
    type-Commutative-Semiring R → UU (l1 ⊔ l2)
  is-linear-combination-family-of-elements-Commutative-Semiring =
    is-linear-combination-family-of-elements-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)
```

### Two-sided linear combinations of a single element in a commutative semiring

```agda
module _
  {l1 : Level} (R : Commutative-Semiring l1) (a : type-Commutative-Semiring R)
  where

  linear-combination-element-Commutative-Semiring :
    UU l1
  linear-combination-element-Commutative-Semiring =
    linear-combination-element-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)

  ev-linear-combination-element-Commutative-Semiring :
    linear-combination-element-Commutative-Semiring →
    type-Commutative-Semiring R
  ev-linear-combination-element-Commutative-Semiring =
    ev-linear-combination-element-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)

  is-linear-combination-element-Commutative-Semiring :
    type-Commutative-Semiring R → UU l1
  is-linear-combination-element-Commutative-Semiring =
    is-linear-combination-element-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)
```

## Properties

### Given a left action of a commutative semiring $R$ on a type $A$ with values in a monoid, the evaluation function preserves concatenation

We assume a monoid here, because we need associativity for the multiplicative operation of the monoid.

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  {A : UU l2} (M : Monoid l3)
  (μ :
    type-Commutative-Semiring R → A →
    type-Commutative-Semiring R → type-Monoid M)
  where

  preserves-concat-ev-monoid-linear-combination-Commutative-Semiring :
    (u v : linear-combination-Commutative-Semiring R A) →
    ev-monoid-linear-combination-Commutative-Semiring R M
      ( μ)
      ( concat-list u v) ＝
    mul-Monoid M
      ( ev-monoid-linear-combination-Commutative-Semiring R M μ u)
      ( ev-monoid-linear-combination-Commutative-Semiring R M μ v)
  preserves-concat-ev-monoid-linear-combination-Commutative-Semiring =
    preserves-concat-ev-monoid-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( M)
      ( μ)

  is-linear-combination-mul-monoid-Commutative-Semiring :
    (x y : type-Monoid M) →
    is-linear-combination-monoid-Commutative-Semiring R M μ x →
    is-linear-combination-monoid-Commutative-Semiring R M μ y →
    is-linear-combination-monoid-Commutative-Semiring R M μ (mul-Monoid M x y)
  is-linear-combination-mul-monoid-Commutative-Semiring  =
    is-linear-combination-mul-monoid-Semiring
      ( semiring-Commutative-Semiring R)
      ( M)
      ( μ)
```

### Evaluation of linear combinations preserves scalar multiplication

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  {A : UU l2} (M : Monoid-With-Commutative-Semiring-Action l3 R)
  (μ :
    type-Commutative-Semiring R → A → type-Commutative-Semiring R →
    type-Monoid-With-Commutative-Semiring-Action R M)
  (α :
    (s r : type-Commutative-Semiring R) (a : A)
    (u v : type-Commutative-Semiring R) →
    μ (mul-Commutative-Semiring R s r) a (mul-Commutative-Semiring R u v) ＝
    action-Monoid-With-Commutative-Semiring-Action R M s (μ r a u) v)
  where

  preserves-mul-ev-linear-combination-Commutative-Semiring :
    (r : type-Commutative-Semiring R)
    (x : linear-combination-Commutative-Semiring R A)
    (u : type-Commutative-Semiring R) →
    ev-monoid-linear-combination-Commutative-Semiring R
      ( monoid-Monoid-With-Commutative-Semiring-Action R M)
      ( μ)
      ( mul-linear-combination-Commutative-Semiring R r x u) ＝
    action-Monoid-With-Commutative-Semiring-Action R M
      ( r)
      ( ev-monoid-linear-combination-Commutative-Semiring R
        ( monoid-Monoid-With-Commutative-Semiring-Action R M)
        ( μ)
        ( x))
      ( u)
  preserves-mul-ev-linear-combination-Commutative-Semiring =
    preserves-mul-ev-linear-combination-Semiring
      ( semiring-Commutative-Semiring R)
      ( M)
      ( μ)
      ( α)

  is-linear-combination-action-Commutative-Semiring :
    (r : type-Commutative-Semiring R)
    (x : type-Monoid-With-Commutative-Semiring-Action R M) →
    (u : type-Commutative-Semiring R) →
    is-linear-combination-monoid-Commutative-Semiring R
      ( monoid-Monoid-With-Commutative-Semiring-Action R M)
      ( μ)
      ( x) →
    is-linear-combination-monoid-Commutative-Semiring R
      ( monoid-Monoid-With-Commutative-Semiring-Action R M)
      ( μ)
      ( action-Monoid-With-Commutative-Semiring-Action R M r x u)
  is-linear-combination-action-Commutative-Semiring =
    is-linear-combination-action-Semiring
      ( semiring-Commutative-Semiring R)
      ( M)
      ( μ)
      ( α)
```

### A linear combination of units in a monoid is the unit

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (M : Monoid-With-Commutative-Semiring-Action l2 R)
  where

  is-linear-combination-of-units-Monoid-With-Commutative-Semiring-Action :
    (x :
      linear-combination-Commutative-Semiring R
        ( type-Monoid-With-Commutative-Semiring-Action R M)) →
    UU l2
  is-linear-combination-of-units-Monoid-With-Commutative-Semiring-Action =
    is-linear-combination-of-units-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  is-unit-ev-is-linear-combination-of-units-Monoid-With-Commutative-Semiring-Action :
    (x :
      linear-combination-Commutative-Semiring R
        ( type-Monoid-With-Commutative-Semiring-Action R M)) →
    is-linear-combination-of-units-Monoid-With-Commutative-Semiring-Action x →
    is-unit-Monoid-With-Commutative-Semiring-Action R M
      ( ev-monoid-linear-combination-Commutative-Semiring R
        ( monoid-Monoid-With-Commutative-Semiring-Action R M)
        ( action-Monoid-With-Commutative-Semiring-Action R M)
        ( x))
  is-unit-ev-is-linear-combination-of-units-Monoid-With-Commutative-Semiring-Action =
    is-unit-ev-is-linear-combination-of-units-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)
```

### A linear combination of zeroes in a semiring is zero

```agda
module _
  {l1 : Level} (R : Commutative-Semiring l1)
  where

  is-linear-combination-of-zeroes-Commutative-Semiring :
    (x :
      linear-combination-Commutative-Semiring R (type-Commutative-Semiring R)) →
    UU l1
  is-linear-combination-of-zeroes-Commutative-Semiring =
    is-linear-combination-of-zeroes-Semiring
      ( semiring-Commutative-Semiring R)

  is-zero-ev-is-linear-combination-of-zeroes-Commutative-Semiring :
    (x :
      linear-combination-Commutative-Semiring R (type-Commutative-Semiring R)) →
    is-linear-combination-of-zeroes-Commutative-Semiring x →
    is-zero-Commutative-Semiring R
      ( ev-monoid-linear-combination-Commutative-Semiring R
        ( additive-monoid-Commutative-Semiring R)
        ( two-sided-mul-Commutative-Semiring R)
        ( x))
  is-zero-ev-is-linear-combination-of-zeroes-Commutative-Semiring =
    is-zero-ev-is-linear-combination-of-zeroes-Semiring
      ( semiring-Commutative-Semiring R)
```

## See also

- [`functoriality-linear-combinations-of-elements-commutative-semirings`](commutative-algebra.functoriality-linear-combinations-of-elements-commutative-semrings.md)
