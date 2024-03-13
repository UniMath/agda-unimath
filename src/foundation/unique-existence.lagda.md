# Unique existence

```agda
module foundation.unique-existence where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Given a predicate `P` on `A` we say there
{{#concept "uniquely exists" Disambiguation="in a subtype" Agda=∃!₍₋₁₎}} _an
`x : A` such that `P x`_, if the [subtype](foundation-core.subtypes.md)
`Σ (x : A), (P x)` is [contractible](foundation-core.contractible-types.md).

More generally, given a type family `B : A → 𝒰` we say there
{{#concept "uniquely exists" Disambiguation="in a total type" Agda=∃!₍₋₁₎}} _an
`x : A` and a `y : B x`_, if the
[total type](foundation.dependent-pair-types.md) `Σ (x : A), (B x)` is
contractible.

## Definitions

### Unique existence in arbitrary type families

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  uniquely-exists-type-family-Prop : Prop (l1 ⊔ l2)
  uniquely-exists-type-family-Prop = is-torsorial-Prop B

  uniquely-exists-type-family : UU (l1 ⊔ l2)
  uniquely-exists-type-family = type-Prop uniquely-exists-type-family-Prop

  is-prop-uniquely-exists-type-family : is-prop uniquely-exists-type-family
  is-prop-uniquely-exists-type-family =
    is-prop-type-Prop uniquely-exists-type-family-Prop
```

### Unique existence in a subtype

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  uniquely-exists-Prop : Prop (l1 ⊔ l2)
  uniquely-exists-Prop = uniquely-exists-type-family-Prop A (type-Prop ∘ P)

  uniquely-exists : UU (l1 ⊔ l2)
  uniquely-exists = type-Prop uniquely-exists-Prop

  is-prop-uniquely-exists : is-prop uniquely-exists
  is-prop-uniquely-exists = is-prop-type-Prop uniquely-exists-Prop

  ∃!₍₋₁₎ : Prop (l1 ⊔ l2)
  ∃!₍₋₁₎ = uniquely-exists-Prop
```

### Components of unique existence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  pair-uniquely-exists : uniquely-exists-type-family A B → Σ A B
  pair-uniquely-exists = center

  pr1-uniquely-exists : uniquely-exists-type-family A B → A
  pr1-uniquely-exists = pr1 ∘ pair-uniquely-exists

  pr2-uniquely-exists :
    (p : uniquely-exists-type-family A B) → B (pr1-uniquely-exists p)
  pr2-uniquely-exists = pr2 ∘ pair-uniquely-exists

  contraction-uniquely-exists :
    (p : uniquely-exists-type-family A B) →
    (q : Σ A B) → pair-uniquely-exists p ＝ q
  contraction-uniquely-exists = contraction
```

## See also

- Unique existence is the indexed analogue of
  [exclusive disjunction](foundation.exclusive-disjunction.md).
- A different name for _unique existence_ is
  [torsoriality](foundation.torsorial-type-families.md).

## External links

- [uniqueness quantifier](https://ncatlab.org/nlab/show/uniqueness+quantifier)
  at $n$Lab
