# Conjunction of types

```agda
module foundation.conjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The {{#concept "conjunction" Disambiguation="of types" Agda=conjunction}} of two
types `A` and `B` is the [proposition](foundation-core.propositions.md) that
both `A` and `B` are [inhabited](foundation.inhabited-types.md). It is defined
as the [propositional truncation](foundation.propositional-truncations.md) of
the [cartesian product](foundation-core.cartesian-product-types.md) of `A` and
`B`

```text
  A ∧ B := ║ A × B ║₋₁
```

The
{{#concept "universal property" Disambiguation="of the conjunction of types" Agda=universal-property-conjunction}}
of the conjunction states that, for every
[proposition](foundation-core.propositions.md) `R`, the evaluation map

```text
  (A ∧ B → R) → (A → B → R)
```

is an [equivalence](foundation.logical-equivalences.md). Hence, the conjunction
satisfies the following exponential law:

\[ R^{(A ∧ B)} ≃ {(R^B)}^A. \]

## Definition

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  conjunction-prop : Prop (l1 ⊔ l2)
  conjunction-prop = trunc-Prop (A × B)

  conjunction : UU (l1 ⊔ l2)
  conjunction = type-Prop conjunction-prop

  is-prop-conjunction : is-prop conjunction
  is-prop-conjunction = is-prop-type-Prop conjunction-prop

  infixr 15 _∧_
  _∧_ : UU (l1 ⊔ l2)
  _∧_ = conjunction
```

**Note**: The symbol used for the conjunction `_∧_` is the
[logical and](https://codepoints.net/U+2227) `∧` (agda-input: `\wedge` `\and`).

### The introduction rule for conjunction

```agda
intro-conjunction :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A → B → A ∧ B
intro-conjunction a b = unit-trunc-Prop (a , b)
```

### The universal property of conjuntions

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  ev-conjunction :
    {l : Level} (R : Prop l) → (A ∧ B → type-Prop R) → A → B → type-Prop R
  ev-conjunction R f a b = f (intro-conjunction a b)

  universal-property-conjunction : UUω
  universal-property-conjunction =
    {l : Level} (R : Prop l) → is-equiv (ev-conjunction R)
```

## Properties

### The conjunction satisfies the universal property of conjuntions

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  rec-conjunction :
    {l : Level} (R : Prop l) → (A → B → type-Prop R) → A ∧ B → type-Prop R
  rec-conjunction R f = rec-trunc-Prop R (λ (a , b) → f a b)

  up-conjunction : universal-property-conjunction A B
  up-conjunction R =
    is-equiv-is-prop
      ( is-prop-function-type (is-prop-type-Prop R))
      ( is-prop-function-type (is-prop-function-type (is-prop-type-Prop R)))
      ( rec-conjunction R)

  equiv-ev-conjunction :
    {l : Level} (R : Prop l) → (A ∧ B → type-Prop R) ≃ (A → B → type-Prop R)
  equiv-ev-conjunction R = (ev-conjunction A B R , up-conjunction R)
```

### If the conjunction holds, then both factors are inhabited

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-left-factor-conjunction : A ∧ B → is-inhabited A
  is-inhabited-left-factor-conjunction =
    rec-trunc-Prop (is-inhabited-Prop A) (unit-trunc-Prop ∘ pr1)

  is-inhabited-right-factor-conjunction : A ∧ B → is-inhabited B
  is-inhabited-right-factor-conjunction =
    rec-trunc-Prop (is-inhabited-Prop B) (unit-trunc-Prop ∘ pr2)
```

### The conjunction is equivalent to the product `is-inhabited A × is-inhabited B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  equiv-product-inhabited-conjunction :
    A ∧ B ≃ is-inhabited A × is-inhabited B
  equiv-product-inhabited-conjunction =
    distributive-trunc-product-Prop

  map-product-inhabited-conjunction :
    A ∧ B → is-inhabited A × is-inhabited B
  map-product-inhabited-conjunction =
    map-equiv equiv-product-inhabited-conjunction

  map-inv-product-inhabited-conjunction :
    is-inhabited A × is-inhabited B → A ∧ B
  map-inv-product-inhabited-conjunction =
    map-inv-equiv equiv-product-inhabited-conjunction
```

### Distributivity of conjunctions over function types

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-distributive-conjunction :
    ((C → A) ∧ (C → B)) → (C → A ∧ B)
  map-distributive-conjunction =
    rec-trunc-Prop
      ( function-Prop C (conjunction-prop A B))
      ( λ (f , g) x → unit-trunc-Prop (f x , g x))
```

The converse of this implication is an instance of
[choice](foundation.axiom-of-choice.md), so we cannot hope to prove it in
general in an intuitionistic setting. However, we can say something weaker:

```agda
  map-distributive-is-inhabited-conjunction :
    (C → is-inhabited A) ∧ (C → is-inhabited B) → (C → A ∧ B)
  map-distributive-is-inhabited-conjunction =
    rec-trunc-Prop
      ( function-Prop C (conjunction-prop A B))
      λ (f , g) x → map-inv-product-inhabited-conjunction (f x , g x)

  map-inv-distributive-is-inhabited-conjunction :
    (C → A ∧ B) → (C → is-inhabited A) ∧ (C → is-inhabited B)
  map-inv-distributive-is-inhabited-conjunction f =
    unit-trunc-Prop
      ( ( is-inhabited-left-factor-conjunction ∘ f) ,
        ( is-inhabited-right-factor-conjunction ∘ f))

  is-equiv-map-distributive-is-inhabited-conjunction :
    is-equiv map-distributive-is-inhabited-conjunction
  is-equiv-map-distributive-is-inhabited-conjunction =
    is-equiv-is-prop
      ( is-prop-conjunction (C → is-inhabited A) (C → is-inhabited B))
      ( is-prop-function-type (is-prop-conjunction A B))
      ( map-inv-distributive-is-inhabited-conjunction)

  distributive-is-inhabited-conjunction :
    (C → is-inhabited A) ∧ (C → is-inhabited B) ≃ (C → A ∧ B)
  distributive-is-inhabited-conjunction =
    ( map-distributive-is-inhabited-conjunction ,
      is-equiv-map-distributive-is-inhabited-conjunction)
```

## See also

- [Conjunction of propositions](foundation.conjunction-propositions.md)
