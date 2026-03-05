# The impredicative encoding of oracle modalities

```agda
module logic.impredicative-encoding-oracle-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.oracle-modalities
open import logic.oracle-reflections
```

</details>

## Idea

Given an oracle `p`, i.e., a predicate `p : A → Prop`, the
{{#concept "impredicative encoding of the oracle modality" Agda=impredicative-oracle-modality}}
`𝒪ₚ` is the operator

```text
  𝒪ₚ s := ∀ (r : Prop), (s ⇒ r) ⇒ (∀ (a : A), (p a ⇒ r) ⇒ r) ⇒ r.
```

We show this operator forms an appropriately large
[oracle modality](logic.oracle-modalities.md). The operator is _impredicative_
in the sense that it produces a large proposition which only has a universal
property with respect to small propositions.

Oracle modalities are considered in the impredicative setting in {{#cite AB26}}.

## Definitions

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  {A : UU l1}
  (p : A → Prop l2)
  where

  type-impredicative-oracle-modality :
    (X : UU l1) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  type-impredicative-oracle-modality X =
    (r : Prop l3) → (X → type-Prop r) →
    ((a : A) → (type-Prop (p a) → type-Prop r) → type-Prop r) →
    type-Prop r

  unit-impredicative-oracle-modality :
    {X : UU l1} →
    X → type-impredicative-oracle-modality X
  unit-impredicative-oracle-modality x r f _ = f x

  is-prop-type-impredicative-oracle-modality :
    {X : UU l1} →
    is-prop (type-impredicative-oracle-modality X)
  is-prop-type-impredicative-oracle-modality =
    is-prop-Π
      ( λ r →
        is-prop-function-type
          ( is-prop-function-type (is-prop-type-Prop r)))

  prop-impredicative-oracle-modality :
    UU l1 → Prop (l1 ⊔ l2 ⊔ lsuc l3)
  prop-impredicative-oracle-modality X =
    ( type-impredicative-oracle-modality X ,
      is-prop-type-impredicative-oracle-modality)
```

## Properties

### The impredicative encodings are oracle modalities

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (p : A → Prop l2)
  where

  ask-impredicative-oracle-modality :
    {l3 : Level} {X : UU l1} →
    (a : A) →
    ( type-Prop (p a) →
      type-impredicative-oracle-modality l3 p X) →
    type-impredicative-oracle-modality l3 p X
  ask-impredicative-oracle-modality a f r unit ask =
    ask a (λ u → f u r unit ask)

  oracle-algebra-impredicative-oracle-modality :
    (l3 : Level) (X : UU l1) →
    oracle-algebra p X (prop-impredicative-oracle-modality l3 p X)
  oracle-algebra-impredicative-oracle-modality l3 X =
    ( unit-impredicative-oracle-modality l3 p ,
      ask-impredicative-oracle-modality)

  ind-impredicative-oracle-modality :
    {l3 : Level} {X : UU l1} →
    dependent-extension-property-oracle-reflection-Level l3 p X
      ( prop-impredicative-oracle-modality l3 p X)
      ( oracle-algebra-impredicative-oracle-modality l3 X)
  ind-impredicative-oracle-modality {l3} {X} Q η ask y =
    y ( Q y)
      ( λ x →
        tr
          ( type-Prop ∘ Q)
          ( eq-type-Prop (prop-impredicative-oracle-modality l3 p X))
          ( η x))
      ( λ a f →
        tr
          ( type-Prop ∘ Q)
          ( eq-type-Prop (prop-impredicative-oracle-modality l3 p X))
          ( ask a (λ _ → y) f))

  impredicative-oracle-reflection :
    (l3 : Level) (X : UU l1) →
    oracle-reflection (l1 ⊔ l2 ⊔ lsuc l3) l3 p X
  impredicative-oracle-reflection l3 X =
    ( prop-impredicative-oracle-modality l3 p X ,
      oracle-algebra-impredicative-oracle-modality l3 X ,
      ind-impredicative-oracle-modality)

  impredicative-oracle-modality :
    (l3 : Level) → oracle-modality l1 (l1 ⊔ l2 ⊔ lsuc l3) l3 p
  impredicative-oracle-modality l3 =
    impredicative-oracle-reflection l3
```

## References

{{#bibliography}}
