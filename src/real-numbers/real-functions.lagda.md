# Real functions over a type

```agda
module real-numbers.real-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.dependent-products-abelian-groups

open import metric-spaces.complete-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.metric-spaces

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets

open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Ideas

The space of {{#concept "real functions" Agda=function-ℝ}} over a type `X` is
the type of functions `X → ℝ`. It inherits the following structures from the
[real numbers](real-numbers.dedekind-real-numbers.md):

- [complete metric space](metric-spaces.complete-metric-spaces.md);
- [additive](real-numbers.addition-real-numbers.md) structure;
- [large poset](order-theory.large-posets.md);

## Definitions

### The type of real functions over a type

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  function-ℝ : UU (l1 ⊔ lsuc l2)
  function-ℝ = X → ℝ l2
```

## Properties

### The metric space of real functions over a type

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  complete-metric-space-function-ℝ :
    Complete-Metric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  complete-metric-space-function-ℝ =
    Π-Complete-Metric-Space X (λ _ → complete-metric-space-leq-ℝ l2)

  metric-space-function-ℝ : Metric-Space (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  metric-space-function-ℝ =
    metric-space-Complete-Metric-Space complete-metric-space-function-ℝ

  set-function-ℝ : Set (l1 ⊔ lsuc l2)
  set-function-ℝ = set-Metric-Space metric-space-function-ℝ

  neighborhood-function-ℝ : ℚ⁺ → Relation (l1 ⊔ l2) (function-ℝ l2 X)
  neighborhood-function-ℝ = neighborhood-Metric-Space metric-space-function-ℝ
```

### Pointwise addition of real functions

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1)
  (f : function-ℝ l2 X) (g : function-ℝ l3 X)
  where

  add-function-ℝ : function-ℝ (l2 ⊔ l3) X
  add-function-ℝ x = add-ℝ (f x) (g x)
```

### Ordering of real functions

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  (f : function-ℝ l2 X) (g : function-ℝ l3 X)
  where

  leq-prop-function-ℝ : Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-function-ℝ = Π-Prop X (λ x → leq-ℝ-Prop (f x) (g x))

  leq-function-ℝ : UU (l1 ⊔ l2 ⊔ l3)
  leq-function-ℝ = type-Prop leq-prop-function-ℝ
```

### Inequality of real functions is reflexive

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  refl-leq-function-ℝ :
    (f : function-ℝ l2 X) → leq-function-ℝ f f
  refl-leq-function-ℝ f x = refl-leq-ℝ (f x)
```

### Inequality of real functions is antisymmetric

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  (f g : function-ℝ l2 X)
  where

  antisymmetric-leq-function-ℝ :
    leq-function-ℝ f g →
    leq-function-ℝ g f →
    f ＝ g
  antisymmetric-leq-function-ℝ I J =
    eq-htpy (λ x → antisymmetric-leq-ℝ (f x) (g x) (I x) (J x))
```

### Inequality of real functions is transitive

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1}
  (f : function-ℝ l2 X)
  (g : function-ℝ l3 X)
  (h : function-ℝ l4 X)
  where

  transitive-leq-function-ℝ :
    leq-function-ℝ g h →
    leq-function-ℝ f g →
    leq-function-ℝ f h
  transitive-leq-function-ℝ I J x =
    transitive-leq-ℝ (f x) (g x) (h x) (I x) (J x)
```

### The large preorder of real functions over a type

```agda
module _
  {l : Level} (X : UU l)
  where

  function-ℝ-Large-Preorder :
    Large-Preorder (λ l' → l ⊔ lsuc l') (λ l1 l2 → l ⊔ l1 ⊔ l2)
  type-Large-Preorder function-ℝ-Large-Preorder = λ l' → function-ℝ l' X
  leq-prop-Large-Preorder function-ℝ-Large-Preorder = leq-prop-function-ℝ
  refl-leq-Large-Preorder function-ℝ-Large-Preorder = refl-leq-function-ℝ
  transitive-leq-Large-Preorder function-ℝ-Large-Preorder =
    transitive-leq-function-ℝ
```

### The large poset of real functions over a type

```agda
module _
  {l : Level} (X : UU l)
  where

  function-ℝ-Large-Poset :
    Large-Poset (λ l' → l ⊔ lsuc l') (λ l1 l2 → l ⊔ l1 ⊔ l2)
  large-preorder-Large-Poset function-ℝ-Large-Poset =
    function-ℝ-Large-Preorder X
  antisymmetric-leq-Large-Poset function-ℝ-Large-Poset =
    antisymmetric-leq-function-ℝ
```
