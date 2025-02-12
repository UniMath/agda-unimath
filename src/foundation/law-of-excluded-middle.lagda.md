# The law of excluded middle

```agda
module foundation.law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.axiom-of-weak-countable-choice
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.weak-law-of-excluded-middle

open import foundation-core.decidable-propositions
open import foundation-core.propositions

open import logic.de-morgan-types

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

The
{{#concept "law of excluded middle" WD="principle of excluded middle" WDID=Q468422 Agda=LEM}}
asserts that any [proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
LEM : (l : Level) → UU (lsuc l)
LEM l = (P : Prop l) → is-decidable (type-Prop P)

prop-LEM : (l : Level) → Prop (lsuc l)
prop-LEM l = Π-Prop (Prop l) (is-decidable-Prop)
```

## Properties

### Given LEM, we obtain a map from the type of propositions to the type of decidable propositions

```agda
decidable-prop-Prop :
  {l : Level} → LEM l → Prop l → Decidable-Prop l
pr1 (decidable-prop-Prop lem P) = type-Prop P
pr1 (pr2 (decidable-prop-Prop lem P)) = is-prop-type-Prop P
pr2 (pr2 (decidable-prop-Prop lem P)) = lem P
```

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-2-Element-Type (λ X → d (pr1 X))
```

### The law of excluded middle implies the weak law of excluded middle

```agda
WLEM-LEM : {l : Level} → LEM l → WLEM l
WLEM-LEM lem P = is-de-morgan-is-decidable (lem P)
```

### The law of excluded middle implies the axiom of weak countable choice

```agda
wcc-lem : {l : Level} → LEM l → level-WCC l
wcc-lem {l} lem F inhab-F contr-le
  with lem (∃ ℕ (λ n → ¬' (is-contr-Prop (type-Set (F n)))))
... | inr none-non-contractible =
  unit-trunc-Prop
    ( λ n →
      rec-coproduct
        ( center)
        ( ex-falso ∘ none-non-contractible ∘ intro-exists n)
        ( lem (is-contr-Prop (type-Set (F n)))))
... | inl one-not-contractible =
  elim-exists
    ( claim)
    ( λ n not-contractible-Fn →
      rec-trunc-Prop
        ( claim)
        ( λ elem-Fn →
          unit-trunc-Prop
            ( λ m →
              trichotomy-le-ℕ
                ( m)
                ( n)
                ( λ m<n →
                  center
                    ( map-right-unit-law-disjunction-is-empty-Prop
                      ( is-contr-Prop (type-Set (F m)))
                      ( is-contr-Prop (type-Set (F n)))
                      ( not-contractible-Fn)
                      ( contr-le m n m<n)))
                ( λ m=n → tr (type-Set ∘ F) (inv m=n) elem-Fn)
                ( λ n<m →
                  center
                    ( map-left-unit-law-disjunction-is-empty-Prop
                      ( is-contr-Prop (type-Set (F n)))
                      ( is-contr-Prop (type-Set (F m)))
                      ( not-contractible-Fn)
                      ( contr-le n m n<m)))))
        ( inhab-F n))
    ( one-not-contractible)
    where
    claim : Prop l
    claim = is-inhabited-Prop ((n : ℕ) → type-Set (F n))
```

## External links

- [Excluded middle](https://ncatlab.org/nlab/show/excluded+middle) at nLab
