# De Morgan propositions

```agda
module logic.de-morgan-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions

open import logic.de-morgans-law

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

In classical logic, i.e., logic where we assume
[the law of excluded middle](foundation.law-of-excluded-middle.md), the _De
Morgan laws_ refers to the pair of logical equivalences

```text
  ¬ (P ∨ Q) ⇔ (¬ P) ∧ (¬ Q)
  ¬ (P ∧ Q) ⇔ (¬ P) ∨ (¬ Q).
```

Out of these in total four logical implications, all but one are validated in
constructive mathematics. The odd one out is

```text
  ¬ (P ∧ Q) ⇒ (¬ P) ∨ (¬ Q).
```

Indeed, this would state that we could constructively deduce from a proof that
neither `P` nor `Q` is true, whether of `P` is false or `Q` is false. This
logical law is what we refer to as [De Morgan's Law](logic.de-morgans-law.md).
If a proposition `P` is such that for every other proposition `Q`, the De Morgan
implication

```text
  ¬ (P ∧ Q) ⇒ (¬ P) ∨ (¬ Q)
```

holds, we say `P` is {{#concept "De Morgan" Disambiguation="proposition"}}.

## Definition

## De Morgan types

```agda
is-de-morgan-type-Level :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
is-de-morgan-type-Level l2 A =
  (B : UU l2) → ¬ (A × B) → disjunction-type (¬ A) (¬ B)

is-de-morgan-type : {l1 : Level} (A : UU l1) → UUω
is-de-morgan-type A =
  {l2 : Level} (B : UU l2) → ¬ (A × B) → disjunction-type (¬ A) (¬ B)

is-prop-is-de-morgan-type-Level :
  {l1 l2 : Level} {A : UU l1} → is-prop (is-de-morgan-type-Level l2 A)
is-prop-is-de-morgan-type-Level {A = A} =
  is-prop-Π (λ B → is-prop-Π (λ p → is-prop-disjunction-type (¬ A) (¬ B)))

is-de-morgan-type-Prop :
  {l1 : Level} (l2 : Level) (A : UU l1) → Prop (l1 ⊔ lsuc l2)
is-de-morgan-type-Prop l2 A =
  ( is-de-morgan-type-Level l2 A , is-prop-is-de-morgan-type-Level)
```

## De Morgan propositions

## Properties

### If a type is De Morgan then its negation is decidable

Indeed, one need only check that `A` and `¬ A` satisfy De Morgan's law, as then
the hypothesis below is just true:

```text
   ¬ (A ∧ ¬ A) ⇒ ¬ A ∨ ¬¬ A.
```

```agda
module _
  {l : Level} (A : UU l)
  where

  is-decidable-neg-is-de-morgan' :
    ({l' : Level} (B : UU l') → ¬ (A × B) → ¬ A + ¬ B) → is-decidable (¬ A)
  is-decidable-neg-is-de-morgan' H = H (¬ A) (λ f → pr2 f (pr1 f))

  is-merely-decidable-neg-satisfies-de-morgan :
    is-de-morgan-type A → is-merely-decidable (¬ A)
  is-merely-decidable-neg-satisfies-de-morgan H = H (¬ A) (λ f → pr2 f (pr1 f))

  is-decidable-neg-is-de-morgan :
    is-de-morgan-type A → is-decidable (¬ A)
  is-decidable-neg-is-de-morgan H =
    rec-trunc-Prop
      ( is-decidable-Prop (neg-type-Prop A))
      ( id)
      ( H (¬ A) (λ f → pr2 f (pr1 f)))
```

### If the negation of a proposition is decidable then it is De Morgan

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-de-morgan-is-decidable-neg-left :
    is-decidable (¬ A) → ¬ (A × B) → ¬ A + ¬ B
  is-de-morgan-is-decidable-neg-left (inl na) f =
    inl na
  is-de-morgan-is-decidable-neg-left (inr nna) f =
    inr (λ y → nna (λ x → f (x , y)))

  is-de-morgan-is-decidable-neg-right :
    is-decidable (¬ B) → ¬ (A × B) → ¬ A + ¬ B
  is-de-morgan-is-decidable-neg-right (inl nb) f =
    inr nb
  is-de-morgan-is-decidable-neg-right (inr nnb) f =
    inl (λ x → nnb (λ y → f (x , y)))

is-de-morgan-is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable (¬ A) → is-de-morgan-type A
is-de-morgan-is-decidable-neg x B q =
  unit-trunc-Prop (is-de-morgan-is-decidable-neg-left x q)
```

## External links

- [De Morgan laws, in constructive mathematics](https://ncatlab.org/nlab/show/De+Morgan+laws#in_constructive_mathematics)
  at $n$Lab
