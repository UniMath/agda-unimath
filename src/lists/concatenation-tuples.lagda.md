# Concatenation of tuples

```agda
module lists.concatenation-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import lists.functoriality-tuples
open import lists.tuples
```

</details>

## Idea

Two [tuples](lists.tuples.md) can be
{{#concept "concatenated" Disambiguation="pairs of tuples" Agda=concat-tuple}}
to form a single tuple. Given a tuple `(u_1, ..., u_n)` and a tuple
`(v_1, ..., v_m)`, their concatenation is the tuple
`(u_1, ..., u_n, v_1, ..., v_m)`.

## Definition

```agda
concat-tuple :
  {n m : ℕ} {l : Level} {A : UU l} →
  tuple A n → tuple A m → tuple A (m +ℕ n)
concat-tuple empty-tuple v = v
concat-tuple (x ∷ u) v = x ∷ (concat-tuple u v)
```

## Properties

### Distributivity

```agda
distributive-map-concat-tuple :
  {n m : ℕ} {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : A → B) → (u : tuple A n) → (v : tuple A m) →
  map-tuple f (concat-tuple u v) ＝ concat-tuple (map-tuple f u) (map-tuple f v)
distributive-map-concat-tuple f empty-tuple v = refl
distributive-map-concat-tuple f (x ∷ u) v =
  ap
    ( λ w → f x ∷ w)
    ( distributive-map-concat-tuple f u v)
```
