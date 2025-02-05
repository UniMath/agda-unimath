# Raising the universe levels of real numbers

```agda
module real-numbers.raising-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

Real numbers have designated universe levels.  For any real number, we can
construct an equivalent real number in any higher universe.

```agda
raise-ℝ : {l1 : Level} → (l2 : Level) → ℝ l1 → ℝ (l1 ⊔ l2)
raise-ℝ l x = real-dedekind-cut {! λ x →   !} {!   !} {!   !}
```
