# Cycle index series of species

```agda
module species.cycle-index-series-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.cyclic-types
```

</details>

## Idea

The cycle index series of a species of types `F` is a type family indexed by
finite families of cyclic types. Note that a finite family of cyclic types `Cᵢ`
uniquely determines a permutation `e` on the disjoint union `C := Σᵢ Cᵢ` of the
underlying types of the `Cᵢ`. This permutation determines an action `F e` on
`F C`. The cycle index series of `F` at the family `Cᵢ` is the type `Fix (F e)`
of fixed points of `F e`.

## Definition

```agda
total-type-family-of-cyclic-types :
  {l1 l2 : Level} (X : UU l1) (C : X → Σ ℕ (Cyclic-Type l2)) →
  UU (l1 ⊔ l2)
total-type-family-of-cyclic-types X C =
  Σ X (λ x → type-Cyclic-Type (pr1 (C x)) (pr2 (C x)))

{-
permutation-family-of-cyclic-types :
  {l1 l2 : Level} (X : 𝔽 l1) (C : type-𝔽 X → Σ ℕ (Cyclic-Type l2)) →
  Aut (total-type-family-of-cyclic-types X C)
permutation-family-of-cyclic-types X C = {!!}

cycle-index-series-species-types :
  {l1 l2 : Level} (F : species-types l1 l2) (X : 𝔽 l1) →
  (type-𝔽 X → Σ ℕ (Cyclic-Type {!!} ∘ succ-ℕ)) →
  UU {!!}
cycle-index-series-species-types F X C =
  Σ {!F (total-type-family-of-cyclic-types X C)!} {!!}
  -}
```
