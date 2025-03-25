# Dependent products of propositions

```agda
module foundation.dependent-products-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
```

</details>

## Idea

Given a family of [propositions](foundation-core.propositions.md) `B : A → 𝒰`,
then the dependent product `Π A B` is again a proposition.

## Definitions

### Products of families of propositions are propositions

```agda
abstract
  is-prop-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)
  is-prop-Π H =
    is-prop-is-proof-irrelevant
      ( λ f → is-contr-Π (λ x → is-proof-irrelevant-is-prop (H x) (f x)))

module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  type-Π-Prop : UU (l1 ⊔ l2)
  type-Π-Prop = (x : A) → type-Prop (P x)

  is-prop-Π-Prop : is-prop type-Π-Prop
  is-prop-Π-Prop = is-prop-Π (λ x → is-prop-type-Prop (P x))

  Π-Prop : Prop (l1 ⊔ l2)
  pr1 Π-Prop = type-Π-Prop
  pr2 Π-Prop = is-prop-Π-Prop
```

We now repeat the above for implicit Π-types.

```agda
abstract
  is-prop-implicit-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-prop (B x)) → is-prop ({x : A} → B x)
  is-prop-implicit-Π H =
    is-prop-equiv
      ( ( λ f x → f {x}) ,
        ( is-equiv-is-invertible (λ g {x} → g x) (refl-htpy) (refl-htpy)))
      ( is-prop-Π H)

module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  type-implicit-Π-Prop : UU (l1 ⊔ l2)
  type-implicit-Π-Prop = {x : A} → type-Prop (P x)

  is-prop-implicit-Π-Prop : is-prop type-implicit-Π-Prop
  is-prop-implicit-Π-Prop =
    is-prop-implicit-Π (λ x → is-prop-type-Prop (P x))

  implicit-Π-Prop : Prop (l1 ⊔ l2)
  pr1 implicit-Π-Prop = type-implicit-Π-Prop
  pr2 implicit-Π-Prop = is-prop-implicit-Π-Prop
```

### The type of functions into a proposition is a proposition

```agda
abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type H = is-prop-Π (λ _ → H)

type-function-Prop :
  {l1 l2 : Level} → UU l1 → Prop l2 → UU (l1 ⊔ l2)
type-function-Prop A P = A → type-Prop P

is-prop-function-Prop :
  {l1 l2 : Level} {A : UU l1} (P : Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-function-Prop P =
  is-prop-function-type (is-prop-type-Prop P)

function-Prop :
  {l1 l2 : Level} → UU l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (function-Prop A P) = type-function-Prop A P
pr2 (function-Prop A P) = is-prop-function-Prop P

type-hom-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → UU (l1 ⊔ l2)
type-hom-Prop P = type-function-Prop (type-Prop P)

is-prop-hom-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  is-prop (type-hom-Prop P Q)
is-prop-hom-Prop P = is-prop-function-Prop

hom-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (hom-Prop P Q) = type-hom-Prop P Q
pr2 (hom-Prop P Q) = is-prop-hom-Prop P Q

infixr 5 _⇒_
_⇒_ = hom-Prop
```

### The type of equivalences between two propositions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-equiv-is-prop : is-prop A → is-prop B → is-prop (A ≃ B)
  is-prop-equiv-is-prop H K =
    is-prop-Σ
      ( is-prop-function-type K)
      ( λ f →
        is-prop-product
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ g → is-prop-is-contr (is-contr-Π (λ y → K (f (g y)) y))))
          ( is-prop-Σ
            ( is-prop-function-type H)
            ( λ h → is-prop-is-contr (is-contr-Π (λ x → H (h (f x)) x)))))

type-equiv-Prop :
  { l1 l2 : Level} (P : Prop l1) (Q : Prop l2) → UU (l1 ⊔ l2)
type-equiv-Prop P Q = (type-Prop P) ≃ (type-Prop Q)

abstract
  is-prop-type-equiv-Prop :
    {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
    is-prop (type-equiv-Prop P Q)
  is-prop-type-equiv-Prop P Q =
    is-prop-equiv-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q)

equiv-Prop :
  { l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
pr1 (equiv-Prop P Q) = type-equiv-Prop P Q
pr2 (equiv-Prop P Q) = is-prop-type-equiv-Prop P Q
```

### A type is a proposition if and only if the type of its endomaps is contractible

```agda
abstract
  is-contr-endomaps-is-prop :
    {l : Level} (P : UU l) → is-prop P → is-contr (P → P)
  is-contr-endomaps-is-prop P is-prop-P =
    is-proof-irrelevant-is-prop (is-prop-function-type is-prop-P) id
```

### Being a proposition is a proposition

```agda
abstract
  is-prop-is-prop :
    {l : Level} (A : UU l) → is-prop (is-prop A)
  is-prop-is-prop A = is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-contr))

is-prop-Prop : {l : Level} (A : UU l) → Prop l
pr1 (is-prop-Prop A) = is-prop A
pr2 (is-prop-Prop A) = is-prop-is-prop A
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
