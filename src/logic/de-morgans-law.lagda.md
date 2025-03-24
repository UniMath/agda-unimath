# De Morgan's law

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module logic.de-morgans-law
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.conjunction funext univalence truncations
open import foundation.coproduct-types funext univalence truncations
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.disjunction funext univalence truncations
open import foundation.double-negation funext univalence truncations
open import foundation.empty-types funext univalence truncations
open import foundation.evaluation-functions
open import foundation.function-types funext
open import foundation.logical-equivalences funext
open import foundation.negation funext
open import foundation.universe-levels

open import foundation-core.decidable-propositions funext univalence truncations
open import foundation-core.propositions

open import univalent-combinatorics.2-element-types funext univalence truncations
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
not both of `P` and `Q` are true, which of `P` and `Q` that is false. This
logical law is what we refer to as
{{#concept "De Morgan's Law" Agda=De-Morgans-Law}}.

## Definition

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  de-morgans-law-Prop' : Prop (l1 ⊔ l2)
  de-morgans-law-Prop' =
    neg-type-Prop (A × B) ⇒ (neg-type-Prop A) ∨ (neg-type-Prop B)

  de-morgans-law' : UU (l1 ⊔ l2)
  de-morgans-law' = ¬ (A × B) → disjunction-type (¬ A) (¬ B)

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  de-morgans-law-Prop : Prop (l1 ⊔ l2)
  de-morgans-law-Prop = ¬' (P ∧ Q) ⇒ (¬' P) ∨ (¬' Q)

  de-morgans-law : UU (l1 ⊔ l2)
  de-morgans-law = type-Prop de-morgans-law-Prop

De-Morgans-Law-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
De-Morgans-Law-Level l1 l2 =
  (P : Prop l1) (Q : Prop l2) → de-morgans-law P Q

prop-De-Morgans-Law-Level : (l1 l2 : Level) → Prop (lsuc l1 ⊔ lsuc l2)
prop-De-Morgans-Law-Level l1 l2 =
  Π-Prop
    ( Prop l1)
    ( λ P → Π-Prop (Prop l2) (λ Q → de-morgans-law-Prop P Q))

De-Morgans-Law : UUω
De-Morgans-Law = {l1 l2 : Level} → De-Morgans-Law-Level l1 l2
```

## Properties

### The constructively valid De Morgan's laws

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  forward-implication-constructive-de-morgan : ¬ (A + B) → (¬ A) × (¬ B)
  forward-implication-constructive-de-morgan z = (z ∘ inl) , (z ∘ inr)

  backward-implication-constructive-de-morgan : (¬ A) × (¬ B) → ¬ (A + B)
  backward-implication-constructive-de-morgan (na , nb) (inl x) = na x
  backward-implication-constructive-de-morgan (na , nb) (inr y) = nb y

  constructive-de-morgan : ¬ (A + B) ↔ (¬ A) × (¬ B)
  constructive-de-morgan =
    ( forward-implication-constructive-de-morgan ,
      backward-implication-constructive-de-morgan)

  backward-implication-de-morgan : ¬ A + ¬ B → ¬ (A × B)
  backward-implication-de-morgan (inl na) (x , y) = na x
  backward-implication-de-morgan (inr nb) (x , y) = nb y
```

### Given the hypothesis of De Morgan's law, the conclusion is irrefutable

```agda
double-negation-de-morgan :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → ¬ (A × B) → ¬¬ (¬ A + ¬ B)
double-negation-de-morgan f v =
  v (inl (λ x → v (inr (λ y → f (x , y)))))
```

### De Morgan's law is irrefutable

```agda
is-irrefutable-de-morgans-law :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → ¬¬ (¬ (A × B) → ¬ A + ¬ B)
is-irrefutable-de-morgans-law u =
  u (λ _ → inl (λ x → u (λ f → inr (λ y → f (x , y)))))
```

## See also

- [De Morgan types](logic.de-morgan-types.md)

## External links

- [De Morgan laws, in constructive mathematics](https://ncatlab.org/nlab/show/De+Morgan+laws#in_constructive_mathematics)
  at $n$Lab
