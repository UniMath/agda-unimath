# Double negation stable propositions

```agda
module foundation.double-negation-stable-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.law-of-excluded-middle
open import foundation.negation
open import foundation.subtype-identity-principle
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
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

## Properties

### The empty proposition is double negation stable

```agda
is-double-negation-stable-empty : is-double-negation-stable empty-Prop
is-double-negation-stable-empty e = e (λ where ())
```

### The unit proposition is double negation stable

```agda
is-double-negation-stable-unit : is-double-negation-stable unit-Prop
is-double-negation-stable-unit _ = star
```

### The negation of a type is double negation stable

```agda
is-double-negation-stable-neg :
  {l : Level} (A : UU l) → is-double-negation-stable (neg-type-Prop A)
is-double-negation-stable-neg = double-negation-elim-neg
```

## See also

- [The double negation modality](foundation.double-negation-modality.md)
