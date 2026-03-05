# Oracle modalities

```agda
module logic.oracle-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.oracle-reflections

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given an oracle `p : A → Prop`, the
{{#concept "oracle modality" Agda=oracle-modality}} of `𝒪ₚ` assigns to every
type `X` an [oracle reflection](logic.oracle-reflections.md). This is the least
[proposition](foundation-core.propositions.md) `𝒪ₚX` equipped with operations

1. `unit : X → 𝒪ₚX`
2. `ask : (a : A) → (p a → 𝒪ₚX) → 𝒪ₚX`.

Oracle modalities are considered in the impredicative setting in {{#cite AB26}}.

## Definitions

```agda
module _
  {l1 l2 : Level}
  (l3 l4 l5 : Level)
  {A : UU l1} (p : A → Prop l2)
  where

  oracle-modality : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4 ⊔ lsuc l5)
  oracle-modality = (X : UU l3) → oracle-reflection l4 l5 p X
```

### Basic projection maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l3 l4 l5 p)
  where

  prop-oracle-modality : UU l3 → Prop l4
  prop-oracle-modality X = prop-oracle-reflection p (𝒪ₚ X)

  type-oracle-modality : UU l3 → UU l4
  type-oracle-modality X = type-oracle-reflection p (𝒪ₚ X)

  is-prop-type-oracle-modality : (X : UU l3) → is-prop (type-oracle-modality X)
  is-prop-type-oracle-modality X = is-prop-type-Prop (prop-oracle-modality X)

  oracle-algebra-oracle-modality :
    (X : UU l3) → oracle-algebra p X (prop-oracle-modality X)
  oracle-algebra-oracle-modality X =
    oracle-algebra-oracle-reflection p (𝒪ₚ X)

  unit-oracle-modality : (X : UU l3) → X → type-oracle-modality X
  unit-oracle-modality X = unit-oracle-reflection p (𝒪ₚ X)

  ask-oracle-modality :
    (X : UU l3) (a : A) →
    (type-Prop (p a) → type-oracle-modality X) →
    type-oracle-modality X
  ask-oracle-modality X = ask-oracle-reflection p (𝒪ₚ X)

  ind-oracle-modality :
    (X : UU l3) →
    dependent-extension-property-oracle-reflection-Level l5 p X
      ( prop-oracle-modality X)
      ( oracle-algebra-oracle-modality X)
  ind-oracle-modality X = ind-oracle-reflection p (𝒪ₚ X)

  rec-oracle-modality :
    (X : UU l3) →
    extension-property-oracle-reflection-Level l5 p X
      ( prop-oracle-modality X)
      ( oracle-algebra-oracle-modality X)
  rec-oracle-modality X = rec-oracle-reflection p (𝒪ₚ X)
```

## Properties

### Oracle modalities are uniquely eliminating

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} (p : A → Prop l2)
  (𝒪ₚ : oracle-modality l1 l2 l2 p)
  where

  map-over-identification-unit-oracle-modality :
    {X : UU l1} (P : type-oracle-modality p 𝒪ₚ X → UU l1) →
    {y y' : type-oracle-modality p 𝒪ₚ X} →
    y ＝ y' →
    type-oracle-modality p 𝒪ₚ (P y) →
    type-oracle-modality p 𝒪ₚ (P y')
  map-over-identification-unit-oracle-modality
    P {y} {y'} e =
    rec-oracle-modality p 𝒪ₚ
      ( P y)
      ( prop-oracle-modality p 𝒪ₚ (P y'))
      ( unit-oracle-modality p 𝒪ₚ (P y') ∘ tr P e)
      ( λ a _ → ask-oracle-modality p 𝒪ₚ (P y') a)

  map-inv-precomp-Π-unit-oracle-modality :
    {X : UU l1} (P : type-oracle-modality p 𝒪ₚ X → UU l1) →
    ((x : X) → type-oracle-modality p 𝒪ₚ (P (unit-oracle-modality p 𝒪ₚ X x))) →
    (y : type-oracle-modality p 𝒪ₚ X) →
    type-oracle-modality p 𝒪ₚ (P y)
  map-inv-precomp-Π-unit-oracle-modality
    {X} P f =
    ind-oracle-modality p 𝒪ₚ
      ( X)
      ( λ y → prop-oracle-modality p 𝒪ₚ (P y))
      ( f)
      ( λ a g g* →
        ask-oracle-modality p 𝒪ₚ
          ( P (ask-oracle-modality p 𝒪ₚ X a g))
          ( a)
          ( λ u →
            map-over-identification-unit-oracle-modality P
              ( eq-type-Prop (prop-oracle-modality p 𝒪ₚ X))
              ( g* u)))

  is-local-dependent-type-unit-oracle-modality :
    {X : UU l1} (P : type-oracle-modality p 𝒪ₚ X → UU l1) →
    is-local-dependent-type
      ( unit-oracle-modality p 𝒪ₚ X)
      ( type-oracle-modality p 𝒪ₚ ∘ P)
  is-local-dependent-type-unit-oracle-modality {X} P =
    is-equiv-has-converse-is-prop
      ( is-prop-Π
        ( λ y → is-prop-type-oracle-modality p 𝒪ₚ (P y)))
      ( is-prop-Π
        ( λ x →
          is-prop-type-oracle-modality p 𝒪ₚ
            ( P (unit-oracle-modality p 𝒪ₚ X x))))
      ( map-inv-precomp-Π-unit-oracle-modality P)

  is-uniquely-eliminating-modality-oracle-modality :
    is-uniquely-eliminating-modality (λ {X} → unit-oracle-modality p 𝒪ₚ X)
  is-uniquely-eliminating-modality-oracle-modality P =
    is-local-dependent-type-unit-oracle-modality P

  oracle-uniquely-eliminating-modality :
    uniquely-eliminating-modality l1 l2
  oracle-uniquely-eliminating-modality =
    ( type-oracle-modality p 𝒪ₚ ,
      ( λ {X} → unit-oracle-modality p 𝒪ₚ X) ,
      is-uniquely-eliminating-modality-oracle-modality)
```

## See also

- [The impredicative encoding of oracle modalities](logic.impredicative-encoding-oracle-modalities.md)

## References

{{#bibliography}}
