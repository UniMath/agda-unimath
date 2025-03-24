# Propositions

```agda
module foundation-core.propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality-axiom
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A type is a {{#concept "proposition" Agda=is-prop}} if its
[identity types](foundation-core.identity-types.md) are
[contractible](foundation-core.contractible-types.md). This condition is
[equivalent](foundation-core.equivalences.md) to the condition that it has up to
identification at most one element.

## Definitions

### The predicate of being a proposition

```agda
is-prop : {l : Level} (A : UU l) → UU l
is-prop A = (x y : A) → is-contr (x ＝ y)
```

### The type of propositions

```agda
Prop :
  (l : Level) → UU (lsuc l)
Prop l = Σ (UU l) is-prop

module _
  {l : Level}
  where

  type-Prop : Prop l → UU l
  type-Prop P = pr1 P

  abstract
    is-prop-type-Prop : (P : Prop l) → is-prop (type-Prop P)
    is-prop-type-Prop P = pr2 P
```

## Examples

We prove here only that any contractible type is a proposition. The fact that
the empty type and the unit type are propositions can be found in

- [`foundation.empty-types`](foundation.empty-types.md), and
- [`foundation.unit-type`](foundation.unit-type.md).

## Properties

### To show that a type is a proposition we may assume it has an element

```agda
abstract
  is-prop-has-element :
    {l1 : Level} {X : UU l1} → (X → is-prop X) → is-prop X
  is-prop-has-element f x y = f x x y
```

### Equivalent characterizations of propositions

```agda
module _
  {l : Level} (A : UU l)
  where

  all-elements-equal : UU l
  all-elements-equal = (x y : A) → x ＝ y

  is-proof-irrelevant : UU l
  is-proof-irrelevant = A → is-contr A

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-prop-all-elements-equal : all-elements-equal A → is-prop A
    pr1 (is-prop-all-elements-equal H x y) = (inv (H x x)) ∙ (H x y)
    pr2 (is-prop-all-elements-equal H x .x) refl = left-inv (H x x)

  abstract
    eq-is-prop' : is-prop A → all-elements-equal A
    eq-is-prop' H x y = pr1 (H x y)

  abstract
    eq-is-prop : is-prop A → {x y : A} → x ＝ y
    eq-is-prop H {x} {y} = eq-is-prop' H x y

  abstract
    is-proof-irrelevant-all-elements-equal :
      all-elements-equal A → is-proof-irrelevant A
    pr1 (is-proof-irrelevant-all-elements-equal H a) = a
    pr2 (is-proof-irrelevant-all-elements-equal H a) = H a

  abstract
    is-proof-irrelevant-is-prop : is-prop A → is-proof-irrelevant A
    is-proof-irrelevant-is-prop =
      is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

  abstract
    is-prop-is-proof-irrelevant : is-proof-irrelevant A → is-prop A
    is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

  abstract
    eq-is-proof-irrelevant : is-proof-irrelevant A → all-elements-equal A
    eq-is-proof-irrelevant = eq-is-prop' ∘ is-prop-is-proof-irrelevant

abstract
  eq-type-Prop : {l : Level} (P : Prop l) → {x y : type-Prop P} → x ＝ y
  eq-type-Prop P = eq-is-prop (is-prop-type-Prop P)

abstract
  is-proof-irrelevant-type-Prop :
    {l : Level} (P : Prop l) → is-proof-irrelevant (type-Prop P)
  is-proof-irrelevant-type-Prop P =
    is-proof-irrelevant-is-prop (is-prop-type-Prop P)
```

### Propositions are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv : {f : A → B} → is-equiv f → is-prop B → is-prop A
    is-prop-is-equiv {f} E H =
      is-prop-is-proof-irrelevant
        ( λ a → is-contr-is-equiv B f E (is-proof-irrelevant-is-prop H (f a)))

  abstract
    is-prop-equiv : A ≃ B → is-prop B → is-prop A
    is-prop-equiv (f , is-equiv-f) = is-prop-is-equiv is-equiv-f

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-equiv' : {f : A → B} → is-equiv f → is-prop A → is-prop B
    is-prop-is-equiv' E H =
      is-prop-is-equiv (is-equiv-map-inv-is-equiv E) H

  abstract
    is-prop-equiv' : A ≃ B → is-prop A → is-prop B
    is-prop-equiv' (f , is-equiv-f) = is-prop-is-equiv' is-equiv-f
```

### Propositions are closed under dependent pair types

```agda
abstract
  is-prop-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → ((x : A) → is-prop (B x)) → is-prop (Σ A B)
  is-prop-Σ H K x y =
    is-contr-equiv'
      ( Eq-Σ x y)
      ( equiv-eq-pair-Σ x y)
      ( is-contr-Σ'
        ( H (pr1 x) (pr1 y))
        ( λ p → K (pr1 y) (tr _ p (pr2 x)) (pr2 y)))

Σ-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : type-Prop P → Prop l2) → Prop (l1 ⊔ l2)
pr1 (Σ-Prop P Q) = Σ (type-Prop P) (λ p → type-Prop (Q p))
pr2 (Σ-Prop P Q) =
  is-prop-Σ
    ( is-prop-type-Prop P)
    ( λ p → is-prop-type-Prop (Q p))
```

### If `Σ A B` is a proposition and there is a section `(x : A) → B x` then `A` is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s : (x : A) → B x)
  where

  is-proof-irrelevant-base-is-proof-irrelevant-Σ' :
    is-proof-irrelevant (Σ A B) → is-proof-irrelevant A
  is-proof-irrelevant-base-is-proof-irrelevant-Σ' H a =
    is-contr-base-is-contr-Σ' A B s (H (a , s a))

  is-prop-base-is-prop-Σ' : is-prop (Σ A B) → is-prop A
  is-prop-base-is-prop-Σ' H =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-base-is-proof-irrelevant-Σ'
          ( is-proof-irrelevant-is-prop H))
```

### Propositions are closed under cartesian product types

```agda
abstract
  is-prop-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-product H K = is-prop-Σ H (λ x → K)

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  type-product-Prop : UU (l1 ⊔ l2)
  type-product-Prop = type-Prop P × type-Prop Q

  is-prop-product-Prop : is-prop type-product-Prop
  is-prop-product-Prop =
    is-prop-product (is-prop-type-Prop P) (is-prop-type-Prop Q)

  product-Prop : Prop (l1 ⊔ l2)
  product-Prop = (type-product-Prop , is-prop-product-Prop)
```

### A type is a proposition if the type of its endomaps is contractible

```agda
abstract
  is-prop-is-contr-endomaps :
    {l : Level} (P : UU l) → is-contr (P → P) → is-prop P
  is-prop-is-contr-endomaps P H =
    is-prop-all-elements-equal (λ x → htpy-eq (eq-is-contr H))
```

## See also

### Operations on propositions

There is a wide range of operations on propositions due to the rich structure of
intuitionistic logic. Below we give a structured overview of a notable selection
of such operations and their notation in the library.

The list is split into two sections, the first consists of operations that
generalize to arbitrary types and even sufficiently nice
[subuniverses](foundation.subuniverses.md), such as
$n$-[types](foundation-core.truncated-types.md).

| Name                                                        | Operator on types | Operator on propositions/subtypes |
| ----------------------------------------------------------- | ----------------- | --------------------------------- |
| [Dependent sum](foundation.dependent-pair-types.md)         | `Σ`               | `Σ-Prop`                          |
| [Dependent product](foundation.dependent-function-types.md) | `Π`               | `Π-Prop`                          |
| [Functions](foundation-core.function-types.md)              | `→`               | `⇒`                               |
| [Logical equivalence](foundation.logical-equivalences.md)   | `↔`               | `⇔`                               |
| [Product](foundation-core.cartesian-product-types.md)       | `×`               | `product-Prop`                    |
| [Join](synthetic-homotopy-theory.joins-of-types.md)         | `*`               | `join-Prop`                       |
| [Exclusive sum](foundation.exclusive-sum.md)                | `exclusive-sum`   | `exclusive-sum-Prop`              |
| [Coproduct](foundation-core.coproduct-types.md)             | `+`               | _N/A_                             |

Note that for many operations in the second section, there is an equivalent
operation on propositions in the first.

| Name                                                                         | Operator on types           | Operator on propositions/subtypes        |
| ---------------------------------------------------------------------------- | --------------------------- | ---------------------------------------- |
| [Initial object](foundation-core.empty-types.md)                             | `empty`                     | `empty-Prop`                             |
| [Terminal object](foundation.unit-type.md)                                   | `unit`                      | `unit-Prop`                              |
| [Existential quantification](foundation.existential-quantification.md)       | `exists-structure`          | `∃`                                      |
| [Unique existential quantification](foundation.uniqueness-quantification.md) | `uniquely-exists-structure` | `∃!`                                     |
| [Universal quantification](foundation.universal-quantification.md)           |                             | `∀'` (equivalent to `Π-Prop`)            |
| [Conjunction](foundation.conjunction.md)                                     |                             | `∧` (equivalent to `product-Prop`)       |
| [Disjunction](foundation.disjunction.md)                                     | `disjunction-type`          | `∨` (equivalent to `join-Prop`)          |
| [Exclusive disjunction](foundation.exclusive-disjunction.md)                 | `xor-type`                  | `⊻` (equivalent to `exclusive-sum-Prop`) |
| [Negation](foundation.negation.md)                                           | `¬`                         | `¬'`                                     |
| [Double negation](foundation.double-negation.md)                             | `¬¬`                        | `¬¬'`                                    |

We can also organize these operations by indexed and binary variants, giving us
the following table:

| Name                   | Binary | Indexed |
| ---------------------- | ------ | ------- |
| Product                | `×`    | `Π`     |
| Conjunction            | `∧`    | `∀'`    |
| Constructive existence | `+`    | `Σ`     |
| Existence              | `∨`    | `∃`     |
| Unique existence       | `⊻`    | `∃!`    |

### Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
