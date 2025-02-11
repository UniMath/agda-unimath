# Propositions

```agda
module foundation.propositions where

open import foundation-core.propositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.logical-equivalences
open import foundation.retracts-of-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.propositional-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### Propositions are `k+1`-truncated for any `k`

```agda
abstract
  is-trunc-is-prop :
    {l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

truncated-type-Prop : {l : Level} (k : 𝕋) → Prop l → Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-Prop k P) = type-Prop P
pr2 (truncated-type-Prop k P) = is-trunc-is-prop k (is-prop-type-Prop P)
```

### Propositions are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-retract-of : A retract-of B → is-prop B → is-prop A
  is-prop-retract-of = is-trunc-retract-of
```

### If a type embeds into a proposition, then it is a proposition

```agda
abstract
  is-prop-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-prop B → is-prop A
  is-prop-is-emb = is-trunc-is-emb neg-two-𝕋

abstract
  is-prop-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ B) → is-prop B → is-prop A
  is-prop-emb = is-trunc-emb neg-two-𝕋
```

### A type is a proposition if and only if it embeds into the unit type

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-prop-is-emb-terminal-map : is-emb (terminal-map A) → is-prop A
    is-prop-is-emb-terminal-map H =
      is-prop-is-emb (terminal-map A) H is-prop-unit

  abstract
    is-emb-terminal-map-is-prop : is-prop A → is-emb (terminal-map A)
    is-emb-terminal-map-is-prop H =
      is-emb-is-prop-map (λ y → is-prop-equiv (equiv-fiber-terminal-map y) H)
```

### Two equivalent types are equivalently propositions

```agda
equiv-is-prop-equiv : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-prop A ≃ is-prop B
equiv-is-prop-equiv {A = A} {B = B} e =
  equiv-iff-is-prop
    ( is-prop-is-prop A)
    ( is-prop-is-prop B)
    ( is-prop-equiv' e)
    ( is-prop-equiv e)
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
