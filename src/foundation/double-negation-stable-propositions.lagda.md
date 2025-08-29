# Double negation stable propositions

```agda
module foundation.double-negation-stable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.retracts-of-types

open import logic.double-negation-elimination
```

</details>

## Idea

A [proposition](foundation-core.propositions.md) `P` is
{{#concept "double negation stable" Disambiguation="proposition" Agda=is-double-negation-stable}}
if the implication

```text
  ¬¬P ⇒ P
```

is true. In other words, if [double negation](foundation.double-negation.md)
elimination is valid for `P`.

## Definitions

### The predicate on a proposition of being double negation stable

```agda
module _
  {l : Level} (P : Prop l)
  where

  is-double-negation-stable-Prop : Prop l
  is-double-negation-stable-Prop = ¬¬' P ⇒ P

  is-double-negation-stable : UU l
  is-double-negation-stable = type-Prop is-double-negation-stable-Prop

  is-prop-is-double-negation-stable : is-prop is-double-negation-stable
  is-prop-is-double-negation-stable =
    is-prop-type-Prop is-double-negation-stable-Prop
```

### The predicate on a type of being a double negation stable proposition

```agda
is-double-negation-stable-prop : {l : Level} → UU l → UU l
is-double-negation-stable-prop X = (is-prop X) × (¬¬ X → X)

is-prop-is-double-negation-stable-prop :
  {l : Level} (X : UU l) → is-prop (is-double-negation-stable-prop X)
is-prop-is-double-negation-stable-prop X =
  is-prop-Σ
    ( is-prop-is-prop X)
    ( λ is-prop-X → is-prop-is-double-negation-stable (X , is-prop-X))

is-double-negation-stable-prop-Prop : {l : Level} → UU l → Prop l
is-double-negation-stable-prop-Prop X =
  ( is-double-negation-stable-prop X , is-prop-is-double-negation-stable-prop X)

module _
  {l : Level} {A : UU l} (H : is-double-negation-stable-prop A)
  where

  is-prop-type-is-double-negation-stable-prop : is-prop A
  is-prop-type-is-double-negation-stable-prop = pr1 H

  has-double-negation-elim-is-double-negation-stable-prop :
    has-double-negation-elim A
  has-double-negation-elim-is-double-negation-stable-prop = pr2 H
```

### The subuniverse of double negation stable propositions

```agda
Double-Negation-Stable-Prop : (l : Level) → UU (lsuc l)
Double-Negation-Stable-Prop l = Σ (UU l) (is-double-negation-stable-prop)

module _
  {l : Level} (P : Double-Negation-Stable-Prop l)
  where

  type-Double-Negation-Stable-Prop : UU l
  type-Double-Negation-Stable-Prop = pr1 P

  is-double-negation-stable-prop-type-Double-Negation-Stable-Prop :
    is-double-negation-stable-prop type-Double-Negation-Stable-Prop
  is-double-negation-stable-prop-type-Double-Negation-Stable-Prop = pr2 P

  is-prop-type-Double-Negation-Stable-Prop :
    is-prop type-Double-Negation-Stable-Prop
  is-prop-type-Double-Negation-Stable-Prop =
    is-prop-type-is-double-negation-stable-prop
      ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop)

  prop-Double-Negation-Stable-Prop : Prop l
  prop-Double-Negation-Stable-Prop =
    ( type-Double-Negation-Stable-Prop ,
      is-prop-type-Double-Negation-Stable-Prop)

  has-double-negation-elim-type-Double-Negation-Stable-Prop :
    has-double-negation-elim type-Double-Negation-Stable-Prop
  has-double-negation-elim-type-Double-Negation-Stable-Prop =
    has-double-negation-elim-is-double-negation-stable-prop
      ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop)
```

## Properties

### The forgetful map from double negation stable propositions to propositions is an embedding

```agda
is-emb-prop-Double-Negation-Stable-Prop :
  {l : Level} → is-emb (prop-Double-Negation-Stable-Prop {l})
is-emb-prop-Double-Negation-Stable-Prop =
  is-emb-tot
    ( λ X →
      is-emb-inclusion-subtype
        ( λ H →
          has-double-negation-elim X , is-prop-has-double-negation-elim H))

emb-prop-Double-Negation-Stable-Prop :
  {l : Level} → Double-Negation-Stable-Prop l ↪ Prop l
emb-prop-Double-Negation-Stable-Prop =
  ( prop-Double-Negation-Stable-Prop , is-emb-prop-Double-Negation-Stable-Prop)
```

### The subuniverse of double negation stable propositions is a set

```agda
is-set-Double-Negation-Stable-Prop :
  {l : Level} → is-set (Double-Negation-Stable-Prop l)
is-set-Double-Negation-Stable-Prop {l} =
  is-set-emb emb-prop-Double-Negation-Stable-Prop is-set-type-Prop

set-Double-Negation-Stable-Prop : (l : Level) → Set (lsuc l)
set-Double-Negation-Stable-Prop l =
  ( Double-Negation-Stable-Prop l , is-set-Double-Negation-Stable-Prop)
```

### Extensionality of double negation stable propositions

```agda
module _
  {l : Level} (P Q : Double-Negation-Stable-Prop l)
  where

  extensionality-Double-Negation-Stable-Prop :
    ( P ＝ Q) ≃
    ( type-Double-Negation-Stable-Prop P ↔ type-Double-Negation-Stable-Prop Q)
  extensionality-Double-Negation-Stable-Prop =
    ( propositional-extensionality
      ( prop-Double-Negation-Stable-Prop P)
      ( prop-Double-Negation-Stable-Prop Q)) ∘e
    ( equiv-ap-emb emb-prop-Double-Negation-Stable-Prop)

  iff-eq-Double-Negation-Stable-Prop :
    P ＝ Q →
    type-Double-Negation-Stable-Prop P ↔ type-Double-Negation-Stable-Prop Q
  iff-eq-Double-Negation-Stable-Prop =
    map-equiv extensionality-Double-Negation-Stable-Prop

  eq-iff-Double-Negation-Stable-Prop :
    (type-Double-Negation-Stable-Prop P → type-Double-Negation-Stable-Prop Q) →
    (type-Double-Negation-Stable-Prop Q → type-Double-Negation-Stable-Prop P) →
    P ＝ Q
  eq-iff-Double-Negation-Stable-Prop f g =
    map-inv-equiv extensionality-Double-Negation-Stable-Prop (pair f g)
```

### Double negation stable propositions are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-double-negation-stable-prop-retract :
    A retract-of B →
    is-double-negation-stable-prop B →
    is-double-negation-stable-prop A
  is-double-negation-stable-prop-retract e H =
    ( is-prop-retract-of e
      ( is-prop-type-is-double-negation-stable-prop H)) ,
    ( has-double-negation-elim-retract e
      ( has-double-negation-elim-is-double-negation-stable-prop H))
```

### Double negation stable propositions are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-double-negation-stable-prop-equiv :
    A ≃ B → is-double-negation-stable-prop B → is-double-negation-stable-prop A
  is-double-negation-stable-prop-equiv e =
    is-double-negation-stable-prop-retract (retract-equiv e)

  is-double-negation-stable-prop-equiv' :
    B ≃ A → is-double-negation-stable-prop B → is-double-negation-stable-prop A
  is-double-negation-stable-prop-equiv' e =
    is-double-negation-stable-prop-retract (retract-inv-equiv e)
```

### The empty proposition is double negation stable

```agda
empty-Double-Negation-Stable-Prop : Double-Negation-Stable-Prop lzero
empty-Double-Negation-Stable-Prop =
  ( empty , is-prop-empty , double-negation-elim-empty)
```

### The unit proposition is double negation stable

```agda
unit-Double-Negation-Stable-Prop : Double-Negation-Stable-Prop lzero
unit-Double-Negation-Stable-Prop =
  ( unit , is-prop-unit , double-negation-elim-unit)
```

```agda
is-double-negation-stable-prop-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-double-negation-stable-prop A
is-double-negation-stable-prop-is-contr H =
  (is-prop-is-contr H , double-negation-elim-is-contr H)
```

### Decidable propositions are double negation stable

```agda
double-negation-stable-prop-Decidable-Prop :
  {l : Level} → Decidable-Prop l → Double-Negation-Stable-Prop l
double-negation-stable-prop-Decidable-Prop (A , H , d) =
  ( A , H , double-negation-elim-is-decidable d)
```

### Negations of types are double negation stable propositions

```agda
neg-type-Double-Negation-Stable-Prop :
  {l : Level} → UU l → Double-Negation-Stable-Prop l
neg-type-Double-Negation-Stable-Prop A =
  ( ¬ A , is-prop-neg , double-negation-elim-neg A)

neg-Double-Negation-Stable-Prop :
  {l : Level} → Double-Negation-Stable-Prop l → Double-Negation-Stable-Prop l
neg-Double-Negation-Stable-Prop P =
  neg-type-Double-Negation-Stable-Prop (type-Double-Negation-Stable-Prop P)
```

### Double negations of types are double negation stable propositions

```agda
double-negation-type-Double-Negation-Stable-Prop :
  {l : Level} → UU l → Double-Negation-Stable-Prop l
double-negation-type-Double-Negation-Stable-Prop A =
  neg-Double-Negation-Stable-Prop (neg-type-Double-Negation-Stable-Prop A)

double-negation-Double-Negation-Stable-Prop :
  {l : Level} → Double-Negation-Stable-Prop l → Double-Negation-Stable-Prop l
double-negation-Double-Negation-Stable-Prop P =
  neg-Double-Negation-Stable-Prop (neg-Double-Negation-Stable-Prop P)
```

### Universal quantification over double negation stable propositions is double negation stable

```agda
is-double-negation-stable-prop-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-double-negation-stable-prop (B a)) →
  is-double-negation-stable-prop ((a : A) → B a)
is-double-negation-stable-prop-Π b =
  ( is-prop-Π (is-prop-type-is-double-negation-stable-prop ∘ b)) ,
  ( double-negation-elim-Π
    ( has-double-negation-elim-is-double-negation-stable-prop ∘ b))

Π-Double-Negation-Stable-Prop :
  {l1 l2 : Level}
  (A : UU l1) (B : A → Double-Negation-Stable-Prop l2) →
  Double-Negation-Stable-Prop (l1 ⊔ l2)
Π-Double-Negation-Stable-Prop A B =
  ( (a : A) → type-Double-Negation-Stable-Prop (B a)) ,
  ( is-double-negation-stable-prop-Π
    ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop ∘ B))
```

### Implication into double negation stable propositions is double negation stable

```agda
is-double-negation-stable-prop-exp :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-double-negation-stable-prop B →
  is-double-negation-stable-prop (A → B)
is-double-negation-stable-prop-exp b =
  is-double-negation-stable-prop-Π (λ _ → b)

exp-Double-Negation-Stable-Prop :
  {l1 l2 : Level}
  (A : UU l1) (B : Double-Negation-Stable-Prop l2) →
  Double-Negation-Stable-Prop (l1 ⊔ l2)
exp-Double-Negation-Stable-Prop A B = Π-Double-Negation-Stable-Prop A (λ _ → B)
```

### Dependent sums of double negation stable propositions over double negation stable propositions are double negation stable

```agda
is-double-negation-stable-prop-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-double-negation-stable-prop A →
  ((a : A) → is-double-negation-stable-prop (B a)) →
  is-double-negation-stable-prop (Σ A B)
is-double-negation-stable-prop-Σ a b =
  ( is-prop-Σ
    ( is-prop-type-is-double-negation-stable-prop a)
    ( is-prop-type-is-double-negation-stable-prop ∘ b)) ,
  ( double-negation-elim-Σ-is-prop-base
    ( is-prop-type-is-double-negation-stable-prop a)
    ( has-double-negation-elim-is-double-negation-stable-prop a)
    ( has-double-negation-elim-is-double-negation-stable-prop ∘ b))

Σ-Double-Negation-Stable-Prop :
  {l1 l2 : Level}
  (A : Double-Negation-Stable-Prop l1)
  (B : type-Double-Negation-Stable-Prop A → Double-Negation-Stable-Prop l2) →
  Double-Negation-Stable-Prop (l1 ⊔ l2)
Σ-Double-Negation-Stable-Prop A B =
  ( Σ ( type-Double-Negation-Stable-Prop A)
      ( type-Double-Negation-Stable-Prop ∘ B)) ,
  ( is-double-negation-stable-prop-Σ
    ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop A)
    ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop ∘ B))
```

### The conjunction of two double negation stable propositions is double negation stable

```agda
is-double-negation-stable-prop-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-double-negation-stable-prop A →
  is-double-negation-stable-prop B →
  is-double-negation-stable-prop (A × B)
is-double-negation-stable-prop-product a b =
  ( is-prop-product
    ( is-prop-type-is-double-negation-stable-prop a)
    ( is-prop-type-is-double-negation-stable-prop b)) ,
  ( double-negation-elim-product
    ( has-double-negation-elim-is-double-negation-stable-prop a)
    ( has-double-negation-elim-is-double-negation-stable-prop b))

product-Double-Negation-Stable-Prop :
  {l1 l2 : Level} →
  Double-Negation-Stable-Prop l1 →
  Double-Negation-Stable-Prop l2 →
  Double-Negation-Stable-Prop (l1 ⊔ l2)
product-Double-Negation-Stable-Prop A B =
  ( ( type-Double-Negation-Stable-Prop A) ×
    ( type-Double-Negation-Stable-Prop B)) ,
  ( is-double-negation-stable-prop-product
    ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop A)
    ( is-double-negation-stable-prop-type-Double-Negation-Stable-Prop B))
```

### Negation has no fixed points on double negation stable propositions

```agda
abstract
  no-fixed-points-neg-Double-Negation-Stable-Prop :
    {l : Level} (P : Double-Negation-Stable-Prop l) →
    ¬ (type-Double-Negation-Stable-Prop P ↔
    ¬ (type-Double-Negation-Stable-Prop P))
  no-fixed-points-neg-Double-Negation-Stable-Prop P =
    no-fixed-points-neg (type-Double-Negation-Stable-Prop P)
```

## See also

- [The double negation modality](foundation.double-negation-modality.md)
- [Irrefutable propositions](foundation.irrefutable-propositions.md) are double
  negation connected types.
