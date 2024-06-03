# Binary relations

```agda
module foundation-core.binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

A {{#concept "binary relation" Agda=Relation}} on a type `A` is a family of types `R x y` depending on
two variables `x y : A`. In the special case where each `R x y` is a
[proposition](foundation-core.propositions.md), we say that the relation is
valued in propositions. Thus, we take a general relation to mean a
_proof-relevant_ relation.

## Definition

### Relations valued in types

```agda
Relation : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
Relation l A = A → A → UU l

total-space-Relation :
  {l1 l : Level} {A : UU l1} → Relation l A → UU (l1 ⊔ l)
total-space-Relation {A = A} R = Σ (A × A) λ (a , a') → R a a'
```

### Relations valued in propositions

```agda
Relation-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Relation-Prop l A = A → A → Prop l

type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Relation l2 A
type-Relation-Prop R x y = pr1 (R x y)

is-prop-type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  (x y : A) → is-prop (type-Relation-Prop R x y)
is-prop-type-Relation-Prop R x y = pr2 (R x y)

total-space-Relation-Prop :
  {l : Level} {l1 : Level} {A : UU l1} → Relation-Prop l A → UU (l ⊔ l1)
total-space-Relation-Prop {A = A} R =
  Σ (A × A) λ (a , a') → type-Relation-Prop R a a'
```

### The predicate of being a reflexive relation

A relation `R` on a type `A` is said to be **reflexive** if it comes equipped
with a function `(x : A) → R x x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-reflexive : UU (l1 ⊔ l2)
  is-reflexive = (x : A) → R x x
```

### The predicate of being a reflexive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be **reflexive**
if its underlying relation is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-reflexive-Relation-Prop : UU (l1 ⊔ l2)
  is-reflexive-Relation-Prop = is-reflexive (type-Relation-Prop R)

  is-prop-is-reflexive-Relation-Prop : is-prop is-reflexive-Relation-Prop
  is-prop-is-reflexive-Relation-Prop =
    is-prop-Π (λ x → is-prop-type-Relation-Prop R x x)
```

### The predicate of being a symmetric relation

A relation `R` on a type `A` is said to be **symmetric** if it comes equipped
with a function `(x y : A) → R x y → R y x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-symmetric : UU (l1 ⊔ l2)
  is-symmetric = (x y : A) → R x y → R y x
```

### The predicate of being a symmetric relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be **symmetric**
if its underlying relation is symmetric.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-symmetric-Relation-Prop : UU (l1 ⊔ l2)
  is-symmetric-Relation-Prop = is-symmetric (type-Relation-Prop R)

  is-prop-is-symmetric-Relation-Prop : is-prop is-symmetric-Relation-Prop
  is-prop-is-symmetric-Relation-Prop =
    is-prop-iterated-Π 3
      ( λ x y r → is-prop-type-Relation-Prop R y x)
```

### The predicate of being a transitive relation

A relation `R` on a type `A` is said to be **transitive** if it comes equipped
with a function `(x y z : A) → R y z → R x y → R x z`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-transitive : UU (l1 ⊔ l2)
  is-transitive = (x y z : A) → R y z → R x y → R x z
```

### The predicate of being a transitive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be **transitive**
if its underlying relation is transitive.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-transitive-Relation-Prop : UU (l1 ⊔ l2)
  is-transitive-Relation-Prop = is-transitive (type-Relation-Prop R)

  is-prop-is-transitive-Relation-Prop : is-prop is-transitive-Relation-Prop
  is-prop-is-transitive-Relation-Prop =
    is-prop-iterated-Π 3
      ( λ x y z →
        is-prop-function-type
          ( is-prop-function-type (is-prop-type-Relation-Prop R x z)))
```

### The predicate of being an irreflexive relation

A relation `R` on a type `A` is said to be **irreflexive** if it comes equipped
with a function `(x : A) → ¬ (R x y)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-irreflexive : UU (l1 ⊔ l2)
  is-irreflexive = (x : A) → ¬ (R x x)
```

### The predicate of being an asymmetric relation

A relation `R` on a type `A` is said to be **asymmetric** if it comes equipped
with a function `(x y : A) → R x y → ¬ (R y x)`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-asymmetric : UU (l1 ⊔ l2)
  is-asymmetric = (x y : A) → R x y → ¬ (R y x)
```

### The predicate of being an antisymmetric relation

A relation `R` on a type `A` is said to be **antisymmetric** if it comes
equipped with a function `(x y : A) → R x y → R y x → x ＝ y`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-antisymmetric : UU (l1 ⊔ l2)
  is-antisymmetric = (x y : A) → R x y → R y x → x ＝ y
```

### The predicate of being an antisymmetric relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be
**antisymmetric** if its underlying relation is antisymmetric.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-antisymmetric-Relation-Prop : UU (l1 ⊔ l2)
  is-antisymmetric-Relation-Prop = is-antisymmetric (type-Relation-Prop R)
```

