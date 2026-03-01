# Sequence-avoiding sets

```agda
module set-theory.sequence-avoiding-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import set-theory.countable-sets
open import set-theory.uncountable-sets
```

</details>

## Idea

A [set](foundation-core.sets.md) `X` is
{{#concept "sequence-avoiding" Disambiguation="set" Agda=is-sequence-avoiding}}
if every [sequence](lists.sequences.md) `a : ℕ → X` misses at least one element
of `X`. [Inhabited](foundation.inhabited-types.md) sequence-avoiding sets are
[uncountable](set-theory.uncountable-sets.md).

## Definitions

### Sequence-avoiding sets

```agda
avoids-sequence-Prop :
  {l : Level} (X : Set l) → (ℕ → type-Set X) → type-Set X → Prop l
avoids-sequence-Prop X a x = Π-Prop ℕ (λ n → nonequal-Prop x (a n))

is-sequence-avoiding-Prop : {l : Level} → Set l → Prop l
is-sequence-avoiding-Prop X =
  Π-Prop
    ( ℕ → type-Set X)
    ( λ a → ∃ (type-Set X) (avoids-sequence-Prop X a))

is-sequence-avoiding : {l : Level} → Set l → UU l
is-sequence-avoiding X = type-Prop (is-sequence-avoiding-Prop X)

is-prop-is-sequence-avoiding :
  {l : Level} (X : Set l) → is-prop (is-sequence-avoiding X)
is-prop-is-sequence-avoiding X =
  is-prop-type-Prop (is-sequence-avoiding-Prop X)
```

### Weakly sequence-avoiding sets

```agda
weakly-avoids-sequence :
  {l : Level} (X : Set l) → (ℕ → type-Set X) → UU l
weakly-avoids-sequence X a =
  is-surjective a →
  ¬¬ type-Prop (∃ (type-Set X) (avoids-sequence-Prop X a))

is-weakly-sequence-avoiding :
  {l : Level} → Set l → UU l
is-weakly-sequence-avoiding X =
  (a : ℕ → type-Set X) → weakly-avoids-sequence X a

module _
  {l : Level} (X : Set l)
  where

  is-weakly-sequence-avoiding-is-sequence-avoiding :
    is-sequence-avoiding X → is-weakly-sequence-avoiding X
  is-weakly-sequence-avoiding-is-sequence-avoiding H a is-surjective-a N =
    N (H a)
```

## Properties

### Sequence-avoiding sets are not directly countable

```agda
module _
  {l : Level} (X : Set l)
  where

  is-not-directly-countable-is-weakly-sequence-avoiding :
    is-weakly-sequence-avoiding X → ¬ is-directly-countable X
  is-not-directly-countable-is-weakly-sequence-avoiding H C =
    apply-universal-property-trunc-Prop C
      ( empty-Prop)
      ( λ (a , is-surjective-a) →
        H a is-surjective-a
          ( λ avoiding-a →
            apply-universal-property-trunc-Prop
              ( avoiding-a)
              ( empty-Prop)
              ( λ (x , x≠a) →
                apply-universal-property-trunc-Prop
                  ( is-surjective-a x)
                  ( empty-Prop)
                  ( λ (n , p) → x≠a n (inv p)))))

  is-not-directly-countable-is-sequence-avoiding :
    is-sequence-avoiding X → ¬ is-directly-countable X
  is-not-directly-countable-is-sequence-avoiding H =
    is-not-directly-countable-is-weakly-sequence-avoiding
      ( is-weakly-sequence-avoiding-is-sequence-avoiding X H)
```

### Inhabited sequence-avoiding sets are uncountable

```agda
module _
  {l : Level} (X : Set l) (x : type-Set X)
  where

  is-uncountable-is-weakly-sequence-avoiding :
    is-weakly-sequence-avoiding X → is-uncountable X
  is-uncountable-is-weakly-sequence-avoiding H C =
    is-not-directly-countable-is-weakly-sequence-avoiding X
      ( H)
      ( is-directly-countable-is-countable X x C)

  is-uncountable-is-sequence-avoiding :
    is-sequence-avoiding X → is-uncountable X
  is-uncountable-is-sequence-avoiding H =
    is-uncountable-is-weakly-sequence-avoiding
      ( is-weakly-sequence-avoiding-is-sequence-avoiding X H)
```

## References

This concept appears in {{#cite BH25}}.

{{#bibliography}}
