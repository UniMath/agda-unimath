# Mere decidable embeddings

```agda
module foundation.mere-decidable-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cantor-schroder-bernstein-decidable-embeddings
open import foundation.decidable-embeddings
open import foundation.functoriality-propositional-truncation
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.propositions

open import order-theory.large-preorders
```

</details>

## Idea

A type `A` {{#concept "merely decidably embeds" Agda=mere-decidable-emb}} into a
type `B` if there [merely exists](foundation.propositional-truncations.md) a
[decidable embedding](foundation.decidable-embeddings.md) of `A` into `B`.

## Definition

```agda
mere-decidable-emb-Prop : {l1 l2 : Level} → UU l1 → UU l2 → Prop (l1 ⊔ l2)
mere-decidable-emb-Prop X Y = trunc-Prop (X ↪ᵈ Y)

mere-decidable-emb : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-decidable-emb X Y = type-Prop (mere-decidable-emb-Prop X Y)

is-prop-mere-decidable-emb :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-decidable-emb X Y)
is-prop-mere-decidable-emb X Y = is-prop-type-Prop (mere-decidable-emb-Prop X Y)
```

## Properties

### Types equipped with mere decidable embeddings form a preordering

```agda
refl-mere-decidable-emb : {l1 : Level} (X : UU l1) → mere-decidable-emb X X
refl-mere-decidable-emb X = unit-trunc-Prop id-decidable-emb

transitive-mere-decidable-emb :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} →
  mere-decidable-emb Y Z → mere-decidable-emb X Y → mere-decidable-emb X Z
transitive-mere-decidable-emb = map-binary-trunc-Prop comp-decidable-emb

mere-decidable-emb-Large-Preorder : Large-Preorder lsuc (_⊔_)
type-Large-Preorder mere-decidable-emb-Large-Preorder l = UU l
leq-prop-Large-Preorder mere-decidable-emb-Large-Preorder =
  mere-decidable-emb-Prop
refl-leq-Large-Preorder mere-decidable-emb-Large-Preorder =
  refl-mere-decidable-emb
transitive-leq-Large-Preorder mere-decidable-emb-Large-Preorder X Y Z =
  transitive-mere-decidable-emb
```

### Assuming WLPO, then types equipped with mere decidable embeddings form a partial ordering

```agda
antisymmetric-mere-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → level-WLPO (l1 ⊔ l2) →
  mere-decidable-emb X Y → mere-decidable-emb Y X → mere-equiv X Y
antisymmetric-mere-decidable-emb wlpo =
  map-binary-trunc-Prop (Cantor-Schröder-Bernstein-WLPO wlpo)
```
