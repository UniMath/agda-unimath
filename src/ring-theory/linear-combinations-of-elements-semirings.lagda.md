# Linear combinations with respect to semirings

```agda
module ring-theory.linear-combinations-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.sets
open import foundation.singleton-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.monoids

open import ring-theory.monoids-with-semiring-action
open import ring-theory.semirings
open import ring-theory.subsets-semirings

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists

open import structured-types.magmas
```

</details>

## Idea

Consider a [semiring](ring-theory.semirings.md) $R$ and a type $A$. A {#concept "linear combination"}} of elements of $A$ is a [list](lists.lists.md) of pairs $(r,a,s)$ consisting of an element $r,s:R$ and an element $a:A$.

Furthermore, if we are given an action $\mu : R \to A \to R \to M$ taking values in a [unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate a linear combination $((r_0,a_0,s_0),\ldots,(r_{n-1},a_{n-1},s_{n-1}))$ by defining

$$
  ev((r_0,a_0,s_0),\ldots,(r_{n-1},a_{n-1},s_{n-1})) :=
  \sum_{i=0}^{n-1} \mu(r_i,a_i,s_i).
$$

To be explicit, linear combinations of elements of a type $A$ have the semiring coefficients on both sides.

## Definitions

### The type of linear combinations

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (A : UU l2)
  where

  linear-combination-Semiring :
    UU (l1 ⊔ l2)
  linear-combination-Semiring =
    list (type-Semiring R × A × type-Semiring R)
```

### Multiplying linear combinations by a scalar from the left, from the right, and from both sides

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) {A : UU l2}
  where

  left-mul-linear-combination-Semiring :
    type-Semiring R →
    linear-combination-Semiring R A →
    linear-combination-Semiring R A
  left-mul-linear-combination-Semiring r =
    map-list (λ (u , a , v) → mul-Semiring R r u , a , v)

  right-mul-linear-combination-Semiring :
    linear-combination-Semiring R A →
    type-Semiring R →
    linear-combination-Semiring R A
  right-mul-linear-combination-Semiring x r =
    map-list (λ (u , a , v) → (u , a , mul-Semiring R v r)) x

  mul-linear-combination-Semiring :
    type-Semiring R →
    linear-combination-Semiring R A →
    type-Semiring R →
    linear-combination-Semiring R A
  mul-linear-combination-Semiring r x s =
    map-list (λ (u , a , v) → (mul-Semiring R r u , a , mul-Semiring R v s)) x
```

### Evaluating linear combinations of elements

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2}
  where

  ev-unital-magma-linear-combination-Semiring :
    (M : Unital-Magma l3)
    (μ : type-Semiring R → A → type-Semiring R → type-Unital-Magma M) →
    linear-combination-Semiring R A → type-Unital-Magma M
  ev-unital-magma-linear-combination-Semiring M μ nil =
    unit-Unital-Magma M
  ev-unital-magma-linear-combination-Semiring M μ (cons (r , a , s) l) =
    mul-Unital-Magma M
      ( μ r a s)
      ( ev-unital-magma-linear-combination-Semiring M μ l)

  ev-monoid-linear-combination-Semiring :
    (M : Monoid l3)
    (μ : type-Semiring R → A → type-Semiring R → type-Monoid M) →
    linear-combination-Semiring R A → type-Monoid M
  ev-monoid-linear-combination-Semiring M =
    ev-unital-magma-linear-combination-Semiring (unital-magma-Monoid M)
```

### The predicate of being a linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2}
  where

  is-linear-combination-Semiring :
    (M : Unital-Magma l3)
    (μ : type-Semiring R → A → type-Semiring R → type-Unital-Magma M) →
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-linear-combination-Semiring M μ =
    fiber (ev-unital-magma-linear-combination-Semiring R M μ)

  is-linear-combination-monoid-Semiring :
    (M : Monoid l3)
    (μ : type-Semiring R → A → type-Semiring R → type-Monoid M) →
    type-Monoid M → UU (l1 ⊔ l2 ⊔ l3)
  is-linear-combination-monoid-Semiring M =
    is-linear-combination-Semiring (unital-magma-Monoid M)
```

### The predicate of being a mere linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Semiring R → A → type-Semiring R → type-Unital-Magma M)
  where

  is-mere-linear-combination-prop-Semiring :
    type-Unital-Magma M → Prop (l1 ⊔ l2 ⊔ l3)
  is-mere-linear-combination-prop-Semiring x =
    trunc-Prop (is-linear-combination-Semiring R M μ x)

  is-mere-linear-combination-Semiring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-mere-linear-combination-Semiring x =
    type-trunc-Prop (is-linear-combination-Semiring R M μ x)

  is-prop-is-mere-linear-combination-Semiring :
    (x : type-Unital-Magma M) →
    is-prop (is-mere-linear-combination-Semiring x)
  is-prop-is-mere-linear-combination-Semiring x =
    is-prop-type-trunc-Prop
```

### Linear combinations of elements of subsets of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  linear-combination-subset-Semiring :
    UU (l1 ⊔ l2)
  linear-combination-subset-Semiring =
    linear-combination-Semiring R (type-subset-Semiring R S)

  two-sided-scalar-multiplication-subset-Semiring :
    type-Semiring R → type-subset-Semiring R S → type-Semiring R →
    type-Semiring R
  two-sided-scalar-multiplication-subset-Semiring r (x , H) u =
    mul-Semiring R (mul-Semiring R r x) u

  ev-linear-combination-subset-Semiring :
    linear-combination-subset-Semiring → type-Semiring R
  ev-linear-combination-subset-Semiring =
    ev-unital-magma-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( two-sided-scalar-multiplication-subset-Semiring)

  is-linear-combination-subset-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-linear-combination-subset-Semiring =
    is-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( two-sided-scalar-multiplication-subset-Semiring)

  is-mere-linear-combination-prop-subset-Semiring :
    type-Semiring R → Prop (l1 ⊔ l2)
  is-mere-linear-combination-prop-subset-Semiring =
    is-mere-linear-combination-prop-Semiring R
      ( additive-unital-magma-Semiring R)
      ( two-sided-scalar-multiplication-subset-Semiring)

  is-mere-linear-combination-subset-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-mere-linear-combination-subset-Semiring  =
    is-mere-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( two-sided-scalar-multiplication-subset-Semiring)
```

### Linear combinations of families of elements in a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) {I : UU l2} (a : I → type-Semiring R)
  where

  linear-combination-family-of-elements-Semiring :
    UU (l1 ⊔ l2)
  linear-combination-family-of-elements-Semiring =
    linear-combination-subset-Semiring R (subtype-im a)

  ev-linear-combination-family-of-elements-Semiring :
    linear-combination-family-of-elements-Semiring → type-Semiring R
  ev-linear-combination-family-of-elements-Semiring =
    ev-linear-combination-subset-Semiring R (trunc-Prop ∘ fiber a)

  is-linear-combination-family-of-elements-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-linear-combination-family-of-elements-Semiring =
    is-linear-combination-subset-Semiring R (trunc-Prop ∘ fiber a)
```

### Linear combinations of a single element in a semiring

Even though left linear combinations and right linear combinations of a single element $a$ in a semiring $R$ can always be written in the form $(r,a)$ or $(a,r)$, resepectively, i.e., any element of the form $r_0a + \cdots + r_{n-1}a$ is equal to an element of the form $ra$ and similar for right linear combinations, the two-sided case is a bit different in that there might be semirings in which an element of the form

$$
  r_0as_0 + \cdots + r_{n-1}as_{n-1}
$$

is not equal to an element of the form $ras$, because the distributivity laws don't apply in this more general case.

```agda
module _
  {l1 : Level} (R : Semiring l1) (a : type-Semiring R)
  where

  linear-combination-element-Semiring :
    UU l1
  linear-combination-element-Semiring =
    linear-combination-subset-Semiring R
      ( subtype-standard-singleton-subtype (set-Semiring R) a)

  ev-linear-combination-element-Semiring :
    linear-combination-element-Semiring → type-Semiring R
  ev-linear-combination-element-Semiring =
    ev-linear-combination-subset-Semiring R
      ( subtype-standard-singleton-subtype (set-Semiring R) a)

  is-linear-combination-element-Semiring :
    type-Semiring R → UU l1
  is-linear-combination-element-Semiring =
    is-linear-combination-subset-Semiring R
      ( subtype-standard-singleton-subtype (set-Semiring R) a)
```

## Properties

### Given a left action of a semiring $R$ on a type $A$ with values in a monoid, the evaluation function preserves concatenation

We assume a monoid here, because we need associativity for the multiplicative operation of the monoid.

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Monoid l3)
  (μ : type-Semiring R → A → type-Semiring R → type-Monoid M)
  where

  preserves-concat-ev-monoid-linear-combination-Semiring :
    (u v : linear-combination-Semiring R A) →
    ev-monoid-linear-combination-Semiring R M
      ( μ)
      ( concat-list u v) ＝
    mul-Monoid M
      ( ev-monoid-linear-combination-Semiring R M μ u)
      ( ev-monoid-linear-combination-Semiring R M μ v)
  preserves-concat-ev-monoid-linear-combination-Semiring nil v =
    inv
      ( left-unit-law-mul-Monoid M
        ( ev-monoid-linear-combination-Semiring R M μ v))
  preserves-concat-ev-monoid-linear-combination-Semiring
    ( cons (r , s , t) u) v =
    ( ap
      ( mul-Monoid M (μ r s t))
      ( preserves-concat-ev-monoid-linear-combination-Semiring u v)) ∙
    ( inv
      ( associative-mul-Monoid M
        ( μ r s t)
        ( ev-monoid-linear-combination-Semiring R M μ u)
        ( ev-monoid-linear-combination-Semiring R M μ v)))

  is-linear-combination-mul-monoid-Semiring :
    (x y : type-Monoid M) →
    is-linear-combination-monoid-Semiring R M μ x →
    is-linear-combination-monoid-Semiring R M μ y →
    is-linear-combination-monoid-Semiring R M μ (mul-Monoid M x y)
  is-linear-combination-mul-monoid-Semiring x y (u , refl) (v , refl) =
    ( concat-list u v ,
      preserves-concat-ev-monoid-linear-combination-Semiring u v)
```

### Evaluation of linear combinations preserves scalar multiplication

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Monoid-With-Semiring-Action l3 R)
  (μ :
    type-Semiring R → A → type-Semiring R →
    type-Monoid-With-Semiring-Action R M)
  (α :
    (s r : type-Semiring R) (a : A) (u v : type-Semiring R) →
    μ (mul-Semiring R s r) a (mul-Semiring R u v) ＝
    action-Monoid-With-Semiring-Action R M s (μ r a u) v)
  where

  preserves-mul-ev-linear-combination-Semiring :
    (r : type-Semiring R) (x : linear-combination-Semiring R A)
    (u : type-Semiring R) →
    ev-monoid-linear-combination-Semiring R
      ( monoid-Monoid-With-Semiring-Action R M)
      ( μ)
      ( mul-linear-combination-Semiring R r x u) ＝
    action-Monoid-With-Semiring-Action R M
      ( r)
      ( ev-monoid-linear-combination-Semiring R
        ( monoid-Monoid-With-Semiring-Action R M)
        ( μ)
        ( x))
      ( u)
  preserves-mul-ev-linear-combination-Semiring r nil u =
    inv (absorption-law-action-Monoid-With-Semiring-Action R M r u)
  preserves-mul-ev-linear-combination-Semiring r (cons (s , x , v) l) u =
    ap-binary
      ( mul-Monoid-With-Semiring-Action R M)
      ( α r s x v u)
      ( preserves-mul-ev-linear-combination-Semiring r l u) ∙
    inv
      ( distributive-action-mul-Monoid-With-Semiring-Action R M r
        ( μ s x v)
        ( ev-monoid-linear-combination-Semiring R
          ( monoid-Monoid-With-Semiring-Action R M)
          ( μ)
          ( l))
        ( u))

  is-linear-combination-action-Semiring :
    (r : type-Semiring R) (x : type-Monoid-With-Semiring-Action R M) →
    (u : type-Semiring R) →
    is-linear-combination-monoid-Semiring R
      ( monoid-Monoid-With-Semiring-Action R M)
      ( μ)
      ( x) →
    is-linear-combination-monoid-Semiring R
      ( monoid-Monoid-With-Semiring-Action R M)
      ( μ)
      ( action-Monoid-With-Semiring-Action R M r x u)
  is-linear-combination-action-Semiring r x u (y , p) =
    ( mul-linear-combination-Semiring R r y u ,
      preserves-mul-ev-linear-combination-Semiring r y u ∙
      ap (λ z → action-Monoid-With-Semiring-Action R M r z u) p)
```

### A linear combination of units in a monoid is the unit

```agda
module _
  {l1 l2 : Level} (R : Semiring l1)
  (M : Monoid-With-Semiring-Action l2 R)
  where

  is-linear-combination-of-units-Monoid-With-Semiring-Action :
    (x : linear-combination-Semiring R (type-Monoid-With-Semiring-Action R M)) →
    UU l2
  is-linear-combination-of-units-Monoid-With-Semiring-Action nil =
    raise-unit l2
  is-linear-combination-of-units-Monoid-With-Semiring-Action
    ( cons (r , x , u) y) =
    is-unit-Monoid-With-Semiring-Action R M x ×
    is-linear-combination-of-units-Monoid-With-Semiring-Action y

  is-unit-ev-is-linear-combination-of-units-Monoid-With-Semiring-Action :
    (x : linear-combination-Semiring R (type-Monoid-With-Semiring-Action R M)) →
    is-linear-combination-of-units-Monoid-With-Semiring-Action x →
    is-unit-Monoid-With-Semiring-Action R M
      ( ev-monoid-linear-combination-Semiring R
        ( monoid-Monoid-With-Semiring-Action R M)
        ( action-Monoid-With-Semiring-Action R M)
        ( x))
  is-unit-ev-is-linear-combination-of-units-Monoid-With-Semiring-Action nil _ =
    refl
  is-unit-ev-is-linear-combination-of-units-Monoid-With-Semiring-Action
    ( cons (r , x , u) y) (refl , K) =
    ap
      ( mul-Monoid-With-Semiring-Action' R M _)
      ( absorption-law-action-Monoid-With-Semiring-Action R M r u) ∙
    left-unit-law-mul-Monoid-With-Semiring-Action R M _ ∙
    is-unit-ev-is-linear-combination-of-units-Monoid-With-Semiring-Action y K
```

### A linear combination of zeroes in a semiring is zero

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-linear-combination-of-zeroes-Semiring :
    (x : linear-combination-Semiring R (type-Semiring R)) → UU l1
  is-linear-combination-of-zeroes-Semiring =
    is-linear-combination-of-units-Monoid-With-Semiring-Action R
      ( additive-monoid-with-semiring-action-Semiring R)

  is-zero-ev-is-linear-combination-of-zeroes-Semiring :
    (x : linear-combination-Semiring R (type-Semiring R)) →
    is-linear-combination-of-zeroes-Semiring x →
    is-zero-Semiring R
      ( ev-monoid-linear-combination-Semiring R
        ( additive-monoid-Semiring R)
        ( action-additive-monoid-with-semiring-action-Semiring R)
        ( x))
  is-zero-ev-is-linear-combination-of-zeroes-Semiring =
    is-unit-ev-is-linear-combination-of-units-Monoid-With-Semiring-Action R
      ( additive-monoid-with-semiring-action-Semiring R)
```

## See also

- [`functoriality-linear-combinations-of-elements-semirings`](ring-theory.functoriality-linear-combinations-of-elements-semrings.md)
