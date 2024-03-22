# Reflexive relations

```agda
module foundation.reflexive-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A {{#concept "reflexive relation" Agda=Reflexive-Relation}} on a type `A` is a
type-valued [binary relation](foundation.binary-relations.md) `R : A → A → 𝒰`
[equipped](foundation.structure.md) with a proof `r : (x : A) → R x x`.

## Definition

### The predicate of being a reflexive relation

A relation `R` on a type `A` is said to be _reflexive_ if it comes equipped with
a function `(x : A) → R x x`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-reflexive : UU (l1 ⊔ l2)
  is-reflexive = (x : A) → R x x
```

### The predicate of being a reflexive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be _reflexive_ if
its underlying relation is reflexive.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-reflexive-Relation-Prop : UU (l1 ⊔ l2)
  is-reflexive-Relation-Prop = is-reflexive (type-Relation-Prop R)

  is-prop-is-reflexive-Relation-Prop : is-prop is-reflexive-Relation-Prop
  is-prop-is-reflexive-Relation-Prop =
    is-prop-Π (λ x → is-prop-type-Relation-Prop R x x)
```

### Reflexive relations

```agda
Reflexive-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Reflexive-Relation l2 A = Σ (Relation l2 A) (is-reflexive)

module _
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A)
  where

  rel-Reflexive-Relation : Relation l2 A
  rel-Reflexive-Relation = pr1 R

  is-reflexive-Reflexive-Relation : is-reflexive rel-Reflexive-Relation
  is-reflexive-Reflexive-Relation = pr2 R
```

### The canonical map from the identity types of the base into a reflexive relation

```agda
leq-eq-Reflexive-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A) →
  {x y : A} → x ＝ y → rel-Reflexive-Relation R x y
leq-eq-Reflexive-Relation R {x} refl = is-reflexive-Reflexive-Relation R x
```
