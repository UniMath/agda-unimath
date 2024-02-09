# Transitive binary relations

```agda
module foundation.transitive-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.iterated-dependent-product-types
open import foundation.subtypes
open import foundation.binary-relations
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A
{{#concept "transitive binary relation" Agda=is-transitive Agda=Transitive-Relation}}
is a [relation](foundation.binary-relations.md) `R` on `A` such that for every
triple `x y z : A`, there is a binary operation

```text
  R y z → R x y → R x z.
```

## Definition

### The predicate of being a transitive relation

A relation `R` on a type `A` is said to be
{{#concept "transitive" Disambiguation="relation" Agda=is-transitive}} if it
comes [equipped](foundation.structure.md) with a function
`(x y z : A) → R y z → R x y → R x z`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-transitive : UU (l1 ⊔ l2)
  is-transitive = (x y z : A) → R y z → R x y → R x z
```

### The predicate of being a transitive relation valued in propositions

A relation `R` on a type `A` valued in propositions is said to be
{{#concept "transitive" Disambiguation="relation valued in propositions" Agda=is-transitive-Relation-Prop}}
if its underlying relation is transitive.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-transitive-Relation-Prop : UU (l1 ⊔ l2)
  is-transitive-Relation-Prop = is-transitive (type-Relation-Prop R)

  is-prop-is-transitive-Relation-Prop : is-prop is-transitive-Relation-Prop
  is-prop-is-transitive-Relation-Prop =
    is-prop-iterated-Π 3
      ( λ x y z →
        is-prop-function-type
          ( is-prop-function-type (is-prop-type-Relation-Prop R x z)))
```
