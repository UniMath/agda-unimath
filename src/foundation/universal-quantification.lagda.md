# Universal quantification

```agda
module foundation.universal-quantification where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

Given a type `A` and a type family `B : A → 𝒰` over it, the
{{#concept "universal quantification" Disambiguation="of types" Agda=∀'}}

```text
  ∀ (x : A) (B x)
```

is the [proposition](foundation-core.propositions.md) that there
[merely exists](foundation.inhabited-types.md) a section `(x : A) → B x`.

**Notation.** Because of syntactic limitations of the Agda language, we must use
the notation `∀'` for the universal quantification.

## Definitions

### The universal quantification

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  universal-quantification-prop : Prop (l1 ⊔ l2)
  universal-quantification-prop = trunc-Prop ((x : A) → B x)

  universal-quantification : UU (l1 ⊔ l2)
  universal-quantification = type-Prop universal-quantification-prop

  is-prop-universal-quantification : is-prop universal-quantification
  is-prop-universal-quantification =
    is-prop-type-Prop universal-quantification-prop

  ∀' : UU (l1 ⊔ l2)
  ∀' = universal-quantification
```

### The universal quantification on a subtype

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → Prop l2)
  where

  universal-quantification-Prop : Prop (l1 ⊔ l2)
  universal-quantification-Prop =
    universal-quantification-prop A (type-Prop ∘ B)

  type-universal-quantification-Prop : UU (l1 ⊔ l2)
  type-universal-quantification-Prop = type-Prop universal-quantification-Prop

  is-prop-universal-quantification-Prop :
    is-prop type-universal-quantification-Prop
  is-prop-universal-quantification-Prop =
    is-prop-type-Prop universal-quantification-Prop

  ∀-Prop : Prop (l1 ⊔ l2)
  ∀-Prop = universal-quantification-Prop

  ∀₍₋₁₎ : Prop (l1 ⊔ l2)
  ∀₍₋₁₎ = universal-quantification-Prop
```

## See also

- [Iimplication of types](foundation.implication.md) for the non-dependent
  variant of universal quantification.
