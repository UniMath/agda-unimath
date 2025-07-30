# The axiom of dependent choice

```agda
module foundation.axiom-of-dependent-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.axiom-of-choice
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "axiom of dependent choice" WD="axiom of dependent choice" WDID=Q3303153 Agda=ADC}}
asserts that for every entire [binary relation](foundation.binary-relations.md)
`R` on an [inhabited type](foundation.inhabited-types.md) `A`, there exists
`f : ℕ → A` such that for all `n : ℕ` , `R (f n) (f (succ-ℕ n))`.

## Definition

```agda
module _
  {l1 : Level} (A : Set l1) (inhabited-A : is-inhabited (type-Set A))
  (l2 : Level)
  where

  instance-ADC : UU (l1 ⊔ lsuc l2)
  instance-ADC =
    (R : Relation l2 (type-Set A)) → is-entire-Relation R →
    is-inhabited (Σ (ℕ → type-Set A) (λ f → (n : ℕ) → R (f n) (f (succ-ℕ n))))

level-ADC : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
level-ADC l1 l2 =
  (A : Set l1) → (inhabited-A : is-inhabited (type-Set A)) →
  instance-ADC A inhabited-A l2

ADC : UUω
ADC = {l1 l2 : Level} → level-ADC l1 l2
```

## Properties

### The axiom of choice implies the axiom of dependent choice

```agda
level-ADC-level-AC0 : {l1 l2 : Level} → level-AC0 l1 (l1 ⊔ l2) → level-ADC l1 l2
level-ADC-level-AC0 ac0 A inhabited-A R entire-R =
  let
    open
      do-syntax-trunc-Prop
        ( is-inhabited-Prop
          ( Σ (ℕ → type-Set A) (λ f → (n : ℕ) → R (f n) (f (succ-ℕ n)))))
  in do
    f ← ac0 A (λ a → Σ (type-Set A) (R a)) entire-R
    a₀ ← inhabited-A
    let g = ind-ℕ a₀ (λ _ → pr1 ∘ f)
    unit-trunc-Prop (g , pr2 ∘ f ∘ g)
```

## See also

- [The axiom of choice](foundation.axiom-of-choice.md)
- [The axiom of countable choice](foundation.axiom-of-countable-choice.md)
