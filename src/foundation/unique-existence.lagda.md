# Unique existence

```agda
module foundation.unique-existence where
```

<details><summary>Imports</summary>

```agda
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.function-types
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

  ∃!-Prop : Prop (l1 ⊔ l2)
  ∃!-Prop = is-torsorial-Prop B

  ∃! : UU (l1 ⊔ l2)
  ∃! = type-Prop ∃!-Prop

  is-prop-∃! : is-prop ∃!
  is-prop-∃! = is-prop-type-Prop ∃!-Prop
```

### Unique existence in a subtype

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  uniquely-exists-Prop : Prop (l1 ⊔ l2)
  uniquely-exists-Prop = ∃!-Prop A (type-Prop ∘ P)

  uniquely-exists : UU (l1 ⊔ l2)
  uniquely-exists = type-Prop uniquely-exists-Prop

  is-prop-uniquely-exists : is-prop uniquely-exists
  is-prop-uniquely-exists = is-prop-type-Prop uniquely-exists-Prop

  ∃!₍₋₁₎ : Prop (l1 ⊔ l2)
  ∃!₍₋₁₎ = uniquely-exists-Prop
```

## See also

- Unique existence is the indexed analogue of
  [exclusive disjunction](foundation.exclusive-disjunction.md).

## External links

- [uniqueness quantifier](https://ncatlab.org/nlab/show/uniqueness+quantifier)
  at $n$Lab
