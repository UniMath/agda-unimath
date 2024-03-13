# Universal quantification

```agda
module foundation.universal-quantification where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

Given a type `A` and a [subtype](foundation-core.subtypes.md) `P : A → Prop`,
the
{{#concept "universal quantification" Disambiguation="of types" WDID=Q126695 Agda=∀'}}

```text
  ∀ (x : A) (P x)
```

is the [proposition](foundation-core.propositions.md) that there
[merely exists](foundation.inhabited-types.md) a proof of `P x` for every `x` in
`A`.

**Notation.** Because of syntactic limitations of the Agda language, we use the
notation `∀'` for the universal quantification in formalizations.

## Definitions

### Universal quantification

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  universal-quantification-Prop : Prop (l1 ⊔ l2)
  universal-quantification-Prop = Π-Prop A P

  type-universal-quantification-Prop : UU (l1 ⊔ l2)
  type-universal-quantification-Prop = type-Prop universal-quantification-Prop

  is-prop-universal-quantification-Prop :
    is-prop type-universal-quantification-Prop
  is-prop-universal-quantification-Prop =
    is-prop-type-Prop universal-quantification-Prop

  for-all : UU (l1 ⊔ l2)
  for-all = type-universal-quantification-Prop

  ∀₍₋₁₎ : Prop (l1 ⊔ l2)
  ∀₍₋₁₎ = universal-quantification-Prop
```

### The universal property of universal quantification

The
{{#concept "universal property" Disambiguation="of universal quantification" Agda=universal-property-universal-quantification}}
of the universal quantification `∀ (a : A), P a` states that for every
proposition `R`, the canonical map

```text
  (R → ∀ (a : A), P a) → (∀ (a : A), R → P a)
```

is an [equivalence](foundation.logical-equivalences.md). Indeed, this holds for
any type `R`.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  ev-universal-quantification :
    {l : Level} (B : UU l) →
    for-all A (λ a → function-Prop B (P a)) → B → for-all A P
  ev-universal-quantification R f r a = f a r

  universal-property-universal-quantification : UUω
  universal-property-universal-quantification =
    {l : Level} (R : Prop l) →
    is-equiv (ev-universal-quantification (type-Prop R))
```

## Properties

### Universal quantification satisfies its universal property

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  map-up-universal-quantification :
    {l : Level} {B : UU l} →
    (B → for-all A P) → for-all A (λ a → function-Prop B (P a))
  map-up-universal-quantification f a r = f r a

  is-equiv-ev-universal-quantification :
    {l : Level} {B : UU l} → is-equiv (ev-universal-quantification A P B)
  is-equiv-ev-universal-quantification {B = B} =
    is-equiv-Prop'
      ( ∀₍₋₁₎ A (λ a → function-Prop B (P a)))
      ( function-Prop B (∀₍₋₁₎ A P))
      ( map-up-universal-quantification)

  up-universal-quantification : universal-property-universal-quantification A P
  up-universal-quantification R = is-equiv-ev-universal-quantification
```

## External links

- [universal quantifier](https://ncatlab.org/nlab/show/universal+quantifier) at
  $n$Lab
- [Universal quantification](https://en.wikipedia.org/wiki/Universal_quantification)
  at Wikipedia
