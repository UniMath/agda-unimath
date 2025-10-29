# Mere embeddings

```agda
module foundation.mere-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cantor-schroder-bernstein-escardo
open import foundation.embeddings
open import foundation.functoriality-propositional-truncation
open import foundation.law-of-excluded-middle
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.propositions

open import order-theory.large-preorders
```

</details>

## Idea

A type `A` {{#concept "merely embeds" Agda=mere-emb}} into a type `B` if there
[merely exists](foundation.propositional-truncations.md) an
[embedding](foundation-core.embeddings.md) of `A` into `B`.

## Definition

```agda
mere-emb-Prop : {l1 l2 : Level} → UU l1 → UU l2 → Prop (l1 ⊔ l2)
mere-emb-Prop X Y = trunc-Prop (X ↪ Y)

mere-emb : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
mere-emb X Y = type-Prop (mere-emb-Prop X Y)

is-prop-mere-emb :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → is-prop (mere-emb X Y)
is-prop-mere-emb X Y = is-prop-type-Prop (mere-emb-Prop X Y)
```

## Properties

### Types equipped with mere embeddings form a preordering

```agda
refl-mere-emb : {l1 : Level} (X : UU l1) → mere-emb X X
refl-mere-emb X = unit-trunc-Prop id-emb

transitive-mere-emb :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3} →
  mere-emb Y Z → mere-emb X Y → mere-emb X Z
transitive-mere-emb = map-binary-trunc-Prop comp-emb

mere-emb-Large-Preorder : Large-Preorder lsuc (_⊔_)
mere-emb-Large-Preorder =
  λ where
  .type-Large-Preorder l → UU l
  .leq-prop-Large-Preorder → mere-emb-Prop
  .refl-leq-Large-Preorder →  refl-mere-emb
  .transitive-leq-Large-Preorder X Y Z → transitive-mere-emb
```

### Assuming excluded middle, if there are mere embeddings between `A` and `B` in both directions, then there is a mere equivalence between them

```agda
antisymmetric-mere-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  LEM (l1 ⊔ l2) → mere-emb X Y → mere-emb Y X → mere-equiv X Y
antisymmetric-mere-emb lem =
  map-binary-trunc-Prop (Cantor-Schröder-Bernstein-Escardó lem)
```
