# Elements of tuples

```agda
module lists.elements-of-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.tuples

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the relation of being an
{{#concept "element" Disambiguation="of a tuple" Agda=element-tuple}} of a
[tuple](lists.tuples.md).

## Definition

```agda
module _
  {l : Level}
  {A : UU l}
  where

  data element-tuple : {n : ℕ} → A → tuple A n → UU l where
    is-head-element-tuple :
      {n : ℕ} (a : A) (l : tuple A n) → element-tuple a (a ∷ l)
    is-in-tail-element-tuple :
      {n : ℕ} (a x : A) (l : tuple A n) → element-tuple a l →
      element-tuple a (x ∷ l)

  open element-tuple public

  infix 6 _∈-tuple_
  _∈-tuple_ : {n : ℕ} → A → tuple A n → UU l
  _∈-tuple_ = element-tuple
```

## Properties

### Elements of a tuple have an index

```agda
module _
  {l : Level}
  {A : UU l}
  where

  index-in-tuple : (n : ℕ) → (a : A) → (v : tuple A n) → a ∈-tuple v → Fin n
  index-in-tuple (succ-ℕ n) a (.a ∷ v) (is-head-element-tuple .a .v) =
    inr star
  index-in-tuple (succ-ℕ n) a (x ∷ v) (is-in-tail-element-tuple .a .x .v I) =
    inl (index-in-tuple n a v I)

  eq-component-tuple-index-in-tuple :
    (n : ℕ) (a : A) (v : tuple A n) (I : a ∈-tuple v) →
    a ＝ component-tuple n v (index-in-tuple n a v I)
  eq-component-tuple-index-in-tuple
    (succ-ℕ n) a (.a ∷ v) (is-head-element-tuple .a .v) =
    refl
  eq-component-tuple-index-in-tuple
    (succ-ℕ n) a (x ∷ v) (is-in-tail-element-tuple .a .x .v I) =
    eq-component-tuple-index-in-tuple n a v I
```
