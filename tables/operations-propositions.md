There is a wide range of operations on propositions due to the rich structure of
intuitionistic logic. Below we give a structured overview of a notable selection
of such operations and their notation in the library.

The list is split into two sections, the first consists of operations that
generalize to sufficiently nice [subuniverses](foundation.subuniverses.md), such
as $n$-[types](foundation-core.truncated-types.md), and the second list consists
of operations which generalize to give propositions for arbitrary types.

| Name                                                        | Operator on types | Operator on propositions |
| ----------------------------------------------------------- | ----------------- | ------------------------ |
| [Dependent sum](foundation.dependent-pair-types.md)         | `Σ`               | `Σ₍₋₁₎`                  |
| [Dependent product](foundation.dependent-function-types.md) | `Π`               | `Π₍₋₁₎`                  |
| [Functions](foundation-core.function-types.md)              | `→`               | `→₍₋₁₎`                  |
| [Logical equivalence](foundation.logical-equivalences.md)   | `↔`               | `↔₍₋₁₎`                  |
| [Product](foundation-core.cartesian-product-types.md)       | `×`               | `×₍₋₁₎`                  |
| [Join](synthetic-homotopy-theory.joins-of-types.md)         | `*`               | `*₍₋₁₎`                  |
| [Exclusive sum](foundation.exclusive-sum.md)                | `exclusive-sum`   | `exclusive-sum-Prop`     |
| [Coproduct](foundation-core.coproduct-types.md)             | `+`               | _N/A_                    |

Note that for many operations in the second list, there is an equivalent
operation on propositions in the first list. In these cases, the operation from
the first list is usually preferred.

| Name                                                                   | Operator on types | Operator on propositions                     |
| ---------------------------------------------------------------------- | ----------------- | -------------------------------------------- |
| [Initial object](foundation-core.empty-types.md)                       | `empty`           | `empty-Prop`                                 |
| [Terminal object](foundation.unit-type.md)                             | `unit`            | `unit-Prop`                                  |
| [Existential quantification](foundation.existential-quantification.md) | `∃`               | `∃₍₋₁₎`                                      |
| [Universal quantification](foundation.universal-quantification.md)     | `∀'`              | `∀₍₋₁₎` (equivalent to `Π₍₋₁₎`)              |
| [Implication](foundation.implication.md)                               | `⇒`               | `⇒₍₋₁₎` (equivalent to `→₍₋₁₎`)              |
| [Biimplication](foundation.biimplication.md)                           | `⇔`               | `⇔₍₋₁₎` (equivalent to `↔₍₋₁₎`)              |
| [Conjunction](foundation.conjunction.md)                               | `∧`               | `∧₍₋₁₎` (equivalent to `×₍₋₁₎`)              |
| [Disjunction](foundation.disjunction.md)                               | `∨`               | `∨₍₋₁₎` (equivalent to `*₍₋₁₎`)              |
| [Exclusive disjunction](foundation.exclusive-disjunction.md)           | `⊻`               | `⊻₍₋₁₎` (equivalent to `exclusive-sum-Prop`) |
| [Negation](foundation.negation.md)                                     | `¬`               | `¬₍₋₁₎`                                      |
| [Double negation](foundation.double-negation.md)                       | `¬¬`              | `¬¬₍₋₁₎`                                     |
