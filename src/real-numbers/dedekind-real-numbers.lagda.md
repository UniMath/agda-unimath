# Dedekind real numbers

```agda
module real-numbers.dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A dedekind real number `x` is a pair of maps `(L , U)` from `ℚ` to `Prop`, with
`L` representing all the rationals smaller than `x`, and `U` representing all
the rationals greater than `x`.

## Definition

```agda
is-dedekind-cut-Prop :
  {l : Level} → (ℚ → Prop l) → (ℚ → Prop l) → Prop l
is-dedekind-cut-Prop L U =
  prod-Prop
    ( prod-Prop (exists-Prop ℚ L) (exists-Prop ℚ U))
    ( prod-Prop
      ( prod-Prop
        ( Π-Prop ℚ
          ( λ q →
            iff-Prop
              ( L q)
              ( exists-Prop ℚ (λ r → prod-Prop (le-ℚ-Prop q r) (L r)))))
        ( Π-Prop ℚ
          ( λ r →
            iff-Prop
              ( U r)
              ( exists-Prop ℚ (λ q → prod-Prop (le-ℚ-Prop q r) (U q))))))
      ( prod-Prop
        ( Π-Prop ℚ (λ q → neg-Prop (prod-Prop (L q) (U q))))
        ( Π-Prop ℚ
          ( λ q →
            Π-Prop ℚ
              ( λ r →
                implication-Prop
                  ( le-ℚ-Prop q r)
                  ( disj-Prop (L q) (U r)))))))
                  
is-dedekind-cut :
  {l : Level} → (ℚ → Prop l) → (ℚ → Prop l) → UU l
is-dedekind-cut L U = type-Prop (is-dedekind-cut-Prop L U)

dedekind-ℝ : (l : Level) → UU (lsuc l)
dedekind-ℝ l = Σ (ℚ → Prop l) (λ L → Σ (ℚ → Prop l) (is-dedekind-cut L))
```
