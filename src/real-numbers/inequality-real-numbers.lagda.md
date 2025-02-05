# Inequality on the real numbers

```agda
module real-numbers.inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  leq-ℝ-Prop : Prop (l1 ⊔ l2)
  leq-ℝ-Prop = leq-prop-subtype (lower-cut-ℝ x) (lower-cut-ℝ y)

  leq-ℝ : UU (l1 ⊔ l2)
  leq-ℝ = type-Prop leq-ℝ-Prop
```

## Properties

### Inequality on the real numbers is reflexive

```agda
refl-leq-ℝ : {l : Level} → (x : ℝ l) → leq-ℝ x x
refl-leq-ℝ x = refl-leq-subtype (lower-cut-ℝ x)
```

### Inequality on the real numbers is antisymmetric

```agda
antisymmetric-leq-ℝ : {l : Level} → (x y : ℝ l) → leq-ℝ x y → leq-ℝ y x → x ＝ y
antisymmetric-leq-ℝ x y x≤y y≤x = eq-eq-lower-cut-ℝ x y {!   !}
```
