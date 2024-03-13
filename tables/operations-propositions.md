There is a wide range of operations on propositions due to the rich structure of
intuitionistic logic. Below we give a structured overview of a notable selection
of such operations and their notation in the library.

The list is split into two sections, the first consists of operations that
generalize to arbitrary types and even sufficiently nice
[subuniverses](foundation.subuniverses.md), such as
$n$-[types](foundation-core.truncated-types.md), and the second section consists
of operations that generalize to give propositions for arbitrary types.

| Name                                                        | Operator on types | Operator on propositions |
| ----------------------------------------------------------- | ----------------- | ------------------------ |
| [Dependent sum](foundation.dependent-pair-types.md)         | `Σ`               | `Σ₍₋₁₎`                  |
| [Dependent product](foundation.dependent-function-types.md) | `Π`               | `∀'`                     |
| [Functions](foundation-core.function-types.md)              | `→`               | `→₍₋₁₎`                  |
| [Logical equivalence](foundation.logical-equivalences.md)   | `↔`               | `↔₍₋₁₎`                  |
| [Product](foundation-core.cartesian-product-types.md)       | `×`               |                          |
| [Join](synthetic-homotopy-theory.joins-of-types.md)         | `*`               |                          |
| [Exclusive sum](foundation.exclusive-sum.md)                | `exclusive-sum`   | `exclusive-sum-Prop`     |
| [Coproduct](foundation-core.coproduct-types.md)             | `+`               | _N/A_                    |

Note that for many operations in the second section, there is an equivalent
operation on propositions in the first.

| Name                                                                         | Operator on types             | Operator on propositions                     |
| ---------------------------------------------------------------------------- | ----------------------------- | -------------------------------------------- |
| [Initial object](foundation-core.empty-types.md)                             | `empty`                       | `empty-Prop`                                 |
| [Terminal object](foundation.unit-type.md)                                   | `unit`                        | `unit-Prop`                                  |
| [Existential quantification](foundation.existential-quantification.md)       | `exists-type-family`          | `∃₍₋₁₎`                                      |
| [Unique existential quantification](foundation.uniqueness-quantification.md) | `uniquely-exists-type-family` | `∃!₍₋₁₎`                                     |
| [Universal quantification](foundation.universal-quantification.md)           |                               | `∀'`                                         |
| [Conjunction](foundation.conjunction.md)                                     |                               | `∧₍₋₁₎`                                      |
| [Disjunction](foundation.disjunction.md)                                     | `disjunction-Type`            | `∨₍₋₁₎`                                      |
| [Exclusive disjunction](foundation.exclusive-disjunction.md)                 | `xor-Type`                    | `⊻₍₋₁₎` (equivalent to `exclusive-sum-Prop`) |
| [Negation](foundation.negation.md)                                           | `¬`                           | `¬₍₋₁₎`                                      |
| [Double negation](foundation.double-negation.md)                             | `¬¬`                          | `¬¬₍₋₁₎`                                     |

We can also organize these operations by indexed and binary variants, giving us
the following table:

| Name                   | Indexed | Binary |
| ---------------------- | ------- | ------ |
| Product                | `Π`     | `×`    |
| Conjunction            | `∀`     | `∧`    |
| Constructive existence | `Σ`     | `+`    |
| Existence              | `∃`     | `∨`    |
| Unique existence       | `∃!`    | `⊻`    |
