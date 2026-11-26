# Coproduct types

```agda
module foundation-core.coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "coproduct" Disambiguation="of types"}} of two types `A` and `B`
can be thought of as the disjoint union of `A` and `B`.

## Definition

### Coproduct types

```agda
infixr 10 _+_

data _+_ {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)
  where
  inl : A → A + B
  inr : B → A + B
```

### The induction principle for coproduct types

```agda
ind-coproduct :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A + B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : A + B) → C t
ind-coproduct C f g (inl x) = f x
ind-coproduct C f g (inr x) = g x
```

### The recursion principle for coproduct types

```agda
rec-coproduct :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → C) → (B → C) → (A + B) → C
rec-coproduct {C = C} = ind-coproduct (λ _ → C)
```

### The induction principle for ternary coproduct types

```agda
ind-ternary-coproduct :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} →
  (D : A + B + C → UU l4) →
  ((x : A) → D (inl x)) →
  ((y : B) → D (inr (inl y))) →
  ((z : C) → D (inr (inr z))) →
  (t : A + B + C) →
  D t
ind-ternary-coproduct D f g h =
  ind-coproduct D f
    (ind-coproduct (λ u → D (inr u)) g h)
```

### The recursion principle for ternary coproduct types

```agda
rec-ternary-coproduct :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} →
  (A → D) →
  (B → D) →
  (C → D) →
  A + B + C →
  D
rec-ternary-coproduct {D = D} =
  ind-ternary-coproduct (λ _ → D)
```
