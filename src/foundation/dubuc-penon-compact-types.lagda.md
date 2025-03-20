# Dubuc-Penon compact types

```agda
open import foundation.function-extensionality-axiom

module
  foundation.dubuc-penon-compact-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.disjunction funext
open import foundation.universal-quantification funext
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.subtypes funext
```

</details>

## Idea

A type is said to be
{{#concept "Dubuc-Penon compact" Agda=is-dubuc-penon-compact}} if for every
[proposition](foundation-core.propositions.md) `P` and every
[subtype](foundation-core.subtypes.md) `Q` of `X` such that the
[disjunction](foundation.disjunction.md) `P ∨ Q x` holds for all `x`, then
either `P` is true or `Q` contains every element of `X`.

## Definition

```agda
is-dubuc-penon-compact-Prop :
  {l : Level} (l1 l2 : Level) → UU l → Prop (l ⊔ lsuc l1 ⊔ lsuc l2)
is-dubuc-penon-compact-Prop l1 l2 X =
  ∀'
    ( Prop l1)
    ( λ P →
      ∀'
        ( subtype l2 X)
        ( λ Q → (∀' X (λ x → P ∨ Q x)) ⇒ (P ∨ (∀' X Q))))

is-dubuc-penon-compact :
  {l : Level} (l1 l2 : Level) → UU l → UU (l ⊔ lsuc l1 ⊔ lsuc l2)
is-dubuc-penon-compact l1 l2 X = type-Prop (is-dubuc-penon-compact-Prop l1 l2 X)
```
