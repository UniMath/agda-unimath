# De Morgan propositions

```agda
module logic.de-morgan-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.decidable-propositions

open import logic.de-morgan-types
open import logic.de-morgans-law
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

Equivalently, a proposition is De Morgan if its negation is decidable. Since
this is a [small](foundation.small-types.md) condition, it is frequently more
convenient to use.

## Definition

### The predicate on propositions of being De Morgan

```agda
module _
  {l : Level} (P : UU l)
  where

  is-de-morgan-prop : UU l
  is-de-morgan-prop = is-prop P × is-de-morgan P

  is-prop-is-de-morgan-prop : is-prop is-de-morgan-prop
  is-prop-is-de-morgan-prop =
    is-prop-product (is-prop-is-prop P) (is-prop-is-de-morgan P)

  is-de-morgan-prop-Prop : Prop l
  is-de-morgan-prop-Prop = is-de-morgan-prop , is-prop-is-de-morgan-prop

module _
  {l : Level} {P : UU l} (H : is-de-morgan-prop P)
  where

  is-prop-type-is-de-morgan-prop : is-prop P
  is-prop-type-is-de-morgan-prop = pr1 H

  is-de-morgan-type-is-de-morgan-prop : is-de-morgan P
  is-de-morgan-type-is-de-morgan-prop = pr2 H
```

### The subuniverse of De Morgan propositions

```agda
De-Morgan-Prop : (l : Level) → UU (lsuc l)
De-Morgan-Prop l = Σ (UU l) (is-de-morgan-prop)

module _
  {l : Level} (A : De-Morgan-Prop l)
  where

  type-De-Morgan-Prop : UU l
  type-De-Morgan-Prop = pr1 A

  is-de-morgan-prop-type-De-Morgan-Prop : is-de-morgan-prop type-De-Morgan-Prop
  is-de-morgan-prop-type-De-Morgan-Prop = pr2 A

  is-prop-type-De-Morgan-Prop : is-prop type-De-Morgan-Prop
  is-prop-type-De-Morgan-Prop =
    is-prop-type-is-de-morgan-prop is-de-morgan-prop-type-De-Morgan-Prop

  is-de-morgan-type-De-Morgan-Prop : is-de-morgan type-De-Morgan-Prop
  is-de-morgan-type-De-Morgan-Prop =
    is-de-morgan-type-is-de-morgan-prop is-de-morgan-prop-type-De-Morgan-Prop

  prop-De-Morgan-Prop : Prop l
  prop-De-Morgan-Prop = type-De-Morgan-Prop , is-prop-type-De-Morgan-Prop

  de-morgan-type-De-Morgan-Prop : De-Morgan-Type l
  de-morgan-type-De-Morgan-Prop =
    type-De-Morgan-Prop , is-de-morgan-type-De-Morgan-Prop
```

## Properties

### The forgetful map from De Morgan propositions to propositions is an embedding

```agda
is-emb-prop-De-Morgan-Prop :
  {l : Level} → is-emb (prop-De-Morgan-Prop {l})
is-emb-prop-De-Morgan-Prop =
  is-emb-tot
    ( λ X →
      is-emb-inclusion-subtype (λ _ → is-de-morgan X , is-prop-is-de-morgan X))

emb-prop-De-Morgan-Prop :
  {l : Level} → De-Morgan-Prop l ↪ Prop l
emb-prop-De-Morgan-Prop =
  ( prop-De-Morgan-Prop , is-emb-prop-De-Morgan-Prop)
```

### The subuniverse of De Morgan propositions is a set

```agda
is-set-De-Morgan-Prop : {l : Level} → is-set (De-Morgan-Prop l)
is-set-De-Morgan-Prop {l} =
  is-set-emb emb-prop-De-Morgan-Prop is-set-type-Prop

set-De-Morgan-Prop : (l : Level) → Set (lsuc l)
set-De-Morgan-Prop l = (De-Morgan-Prop l , is-set-De-Morgan-Prop)
```

### Extensionality of De Morgan propositions

```agda
module _
  {l : Level} (P Q : De-Morgan-Prop l)
  where

  extensionality-De-Morgan-Prop :
    (P ＝ Q) ≃ (type-De-Morgan-Prop P ↔ type-De-Morgan-Prop Q)
  extensionality-De-Morgan-Prop =
    ( propositional-extensionality
      ( prop-De-Morgan-Prop P)
      ( prop-De-Morgan-Prop Q)) ∘e
    ( equiv-ap-emb emb-prop-De-Morgan-Prop)

  iff-eq-De-Morgan-Prop : P ＝ Q → type-De-Morgan-Prop P ↔ type-De-Morgan-Prop Q
  iff-eq-De-Morgan-Prop = map-equiv extensionality-De-Morgan-Prop

  eq-iff-De-Morgan-Prop' : type-De-Morgan-Prop P ↔ type-De-Morgan-Prop Q → P ＝ Q
  eq-iff-De-Morgan-Prop' = map-inv-equiv extensionality-De-Morgan-Prop

  eq-iff-De-Morgan-Prop :
    (type-De-Morgan-Prop P → type-De-Morgan-Prop Q) →
    (type-De-Morgan-Prop Q → type-De-Morgan-Prop P) →
    P ＝ Q
  eq-iff-De-Morgan-Prop f g = eq-iff-De-Morgan-Prop' (f , g)
```

### De Morgan propositions are closed under retracts

```agda
is-de-morgan-prop-retract-of :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  P retract-of Q → is-de-morgan-prop Q → is-de-morgan-prop P
is-de-morgan-prop-retract-of R H =
  is-prop-retract-of R (is-prop-type-is-de-morgan-prop H) ,
  is-de-morgan-iff' (iff-retract' R) (is-de-morgan-type-is-de-morgan-prop H)
```

### De Morgan propositions are closed under equivalences

```agda
is-de-morgan-prop-equiv :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  P ≃ Q → is-de-morgan-prop Q → is-de-morgan-prop P
is-de-morgan-prop-equiv e = is-de-morgan-prop-retract-of (retract-equiv e)

is-de-morgan-prop-equiv' :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  Q ≃ P → is-de-morgan-prop Q → is-de-morgan-prop P
is-de-morgan-prop-equiv' e = is-de-morgan-prop-retract-of (retract-inv-equiv e)
```

### Irrefutable propositions are De Morgan

```agda
is-de-morgan-prop-is-irrefutable-prop :
  {l : Level} {P : UU l} → is-irrefutable-prop P → is-de-morgan-prop P
is-de-morgan-prop-is-irrefutable-prop = tot (λ _ → is-de-morgan-is-irrefutable)
```

### Contractible types are De Morgan propositions

```agda
is-de-morgan-prop-is-contr :
  {l : Level} {P : UU l} → is-contr P → is-de-morgan-prop P
is-de-morgan-prop-is-contr H =
  is-de-morgan-prop-is-irrefutable-prop (is-irrefutable-prop-is-contr H)
```

### Empty types are De Morgan propositions

```agda
is-de-morgan-prop-is-empty :
  {l : Level} {P : UU l} → is-empty P → is-de-morgan-prop P
is-de-morgan-prop-is-empty H = is-prop-is-empty H , is-de-morgan-is-empty H
```

### Dependent sums of De Morgan propositions over decidable propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-de-morgan-prop-Σ' :
    is-decidable-prop A → ((x : A) → is-de-morgan (B x)) → is-de-morgan (Σ A B)
  is-de-morgan-prop-Σ' (is-prop-A , inl a) b =
    rec-coproduct
      ( λ nb → inl λ ab → nb (tr B (eq-is-prop is-prop-A) (pr2 ab)))
      ( λ x → inr (λ z → x (λ b → z (a , b))))
      ( b a)
  is-de-morgan-prop-Σ' (is-prop-A , inr na) b = inl (λ ab → na (pr1 ab))

  is-de-morgan-prop-Σ :
    is-decidable-prop A →
    ((x : A) → is-de-morgan-prop (B x)) →
    is-de-morgan-prop (Σ A B)
  is-de-morgan-prop-Σ a b =
    ( is-prop-Σ
      ( is-prop-type-is-decidable-prop a)
      ( is-prop-type-is-de-morgan-prop ∘ b)) ,
    ( is-de-morgan-prop-Σ' a (is-de-morgan-type-is-de-morgan-prop ∘ b))
```

### The negation operation on decidable propositions

```agda
is-de-morgan-prop-neg :
  {l1 : Level} {A : UU l1} → is-de-morgan A → is-de-morgan-prop (¬ A)
is-de-morgan-prop-neg is-de-morgan-A =
  ( is-prop-neg , is-de-morgan-neg is-de-morgan-A)

neg-type-De-Morgan-Prop :
  {l1 : Level} (A : UU l1) → is-de-morgan A → De-Morgan-Prop l1
neg-type-De-Morgan-Prop A is-de-morgan-A =
  ( ¬ A , is-de-morgan-prop-neg is-de-morgan-A)

neg-De-Morgan-Prop :
  {l1 : Level} → De-Morgan-Prop l1 → De-Morgan-Prop l1
neg-De-Morgan-Prop P =
  neg-type-De-Morgan-Prop
    ( type-De-Morgan-Prop P)
    ( is-de-morgan-type-De-Morgan-Prop P)

type-neg-De-Morgan-Prop :
  {l1 : Level} → De-Morgan-Prop l1 → UU l1
type-neg-De-Morgan-Prop P = type-De-Morgan-Prop (neg-De-Morgan-Prop P)
```

### Negation has no fixed points on decidable propositions

```agda
abstract
  no-fixed-points-neg-De-Morgan-Prop :
    {l : Level} (P : De-Morgan-Prop l) →
    ¬ (type-De-Morgan-Prop P ↔ ¬ (type-De-Morgan-Prop P))
  no-fixed-points-neg-De-Morgan-Prop P =
    no-fixed-points-neg (type-De-Morgan-Prop P)
```

## External links

- [De Morgan laws, in constructive mathematics](https://ncatlab.org/nlab/show/De+Morgan+laws#in_constructive_mathematics)
  at $n$Lab
