# The axiom of countable choice

```agda
module foundation.axiom-of-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.axiom-of-choice
open import foundation.unit-type
open import foundation.inhabited-types
open import foundation.binary-relations
open import foundation.identity-types
open import foundation.axiom-of-dependent-choice
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "axiom of countable choice" WD="axiom of countable choice" WDID=Q1000116 Agda=ACω}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `B` indexed by the
[natural numbers](elementary-number-theory.natural-numbers.md) `ℕ`, the type of
sections of that family `(n : ℕ) → B n` is inhabited.

## Definition

```agda
level-ACω : (l : Level) → UU (lsuc l)
level-ACω l =
  (f : ℕ → Inhabited-Type l) →
  is-inhabited ((n : ℕ) → type-Inhabited-Type (f n))

ACω : UUω
ACω = {l : Level} → level-ACω l
```

## Properties

### The axiom of choice implies the axiom of countable choice

```agda
level-ACω-level-AC0 : {l : Level} → level-AC0 lzero l → level-ACω l
level-ACω-level-AC0 ac0 f =
  ac0
    ( ℕ-Set)
    ( λ n → type-Inhabited-Type (f n))
    ( λ n → is-inhabited-type-Inhabited-Type (f n))

ACω-AC0 : AC0 → ACω
ACω-AC0 ac0 = level-ACω-level-AC0 ac0
```

### The axiom of dependent choice implies the axiom of countable choice

```agda
level-ACω-level-ADC : {l : Level} → level-ADC l lzero → level-ACω l
level-ACω-level-ADC {l} adc f =
  let
    A : UU l
    A = Σ ℕ (λ n → type-Inhabited-Type (f n))
    R : A → A → UU lzero
    R = (λ (m , _) (n , _) → n ＝ succ-ℕ m)
    is-entire-R : is-entire-Relation R
    is-entire-R =
      λ (n , _) →
        rec-trunc-Prop
          ( is-inhabited-Prop _)
          ( λ fsn → unit-trunc-Prop ((succ-ℕ n , fsn) , refl))
          ( is-inhabited-type-Inhabited-Type (f (succ-ℕ n)))
  in
    rec-trunc-Prop
      ( is-inhabited-Prop _)
      ( λ (f , Rfnfsn) → unit-trunc-Prop (λ n → {!   !}))
      ( adc A (unit-trunc-Prop (zero-ℕ , {!   !})) R is-entire-R)
```
