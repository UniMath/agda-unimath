# The large poset of subalgebras of an algebra

```agda
module universal-algebra.large-poset-subalgebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.universe-levels

open import order-theory.large-posets

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.large-poset-submodels-of-signatures
open import universal-algebra.signatures
open import universal-algebra.subalgebras
```

</details>

## Idea

[Subalgebras](universal-algebra.subalgebras.md) of an
[algebra](universal-algebra.algebras.md) form a
[large poset](order-theory.large-posets.md) under the containment relation.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  where

  large-poset-Subalgebra :
    Large-Poset (λ l → l1 ⊔ l3 ⊔ lsuc l) (λ l4 l5 → l3 ⊔ l4 ⊔ l5)
  large-poset-Subalgebra =
    large-poset-Submodel-Of-Signature σ (model-Algebra σ T A)

  leq-prop-Subalgebra :
    Large-Relation-Prop (λ l4 l5 → l3 ⊔ l4 ⊔ l5) (λ l → Subalgebra l σ T A)
  leq-prop-Subalgebra = leq-prop-Large-Poset large-poset-Subalgebra

  leq-Subalgebra :
    Large-Relation (λ l4 l5 → l3 ⊔ l4 ⊔ l5) (λ l → Subalgebra l σ T A)
  leq-Subalgebra = leq-Large-Poset large-poset-Subalgebra
```
