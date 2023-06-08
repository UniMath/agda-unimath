# Discrete reflexive relations

```agda
module foundation.discrete-reflexive-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.reflexive-relations
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A reflexive relation `R` on a type `A` is said to be discrete if for every
`x : A` the type `Σ A (R x)` is contractible. The (standard) discrete reflexive
relation on a type is its identity type.

## Definitions

### Discrete reflexive relations

```agda
is-discrete-Reflexive-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A) → Prop (l1 ⊔ l2)
is-discrete-Reflexive-Relation-Prop {A = A} R =
  Π-Prop A (λ x → is-contr-Prop (Σ A (rel-Reflexive-Relation R x)))

is-discrete-Reflexive-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A) → UU (l1 ⊔ l2)
is-discrete-Reflexive-Relation R =
  type-Prop (is-discrete-Reflexive-Relation-Prop R)
```

### The standard discrete reflexive relation

```agda
Δ-Reflexive-Relation :
  {l1 : Level} (A : UU l1) → Reflexive-Relation l1 A
pr1 (Δ-Reflexive-Relation A) = Id
pr2 (Δ-Reflexive-Relation A) x = refl
```
