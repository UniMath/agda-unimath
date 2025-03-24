# Mere embeddings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.mere-embeddings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cantor-schroder-bernstein-escardo funext univalence truncations
open import foundation.embeddings funext
open import foundation.law-of-excluded-middle funext univalence truncations
open import foundation.mere-equivalences funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.universe-levels

open import foundation-core.propositions

open import order-theory.large-preorders funext univalence truncations
```

</details>

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
transitive-mere-emb g f =
  apply-universal-property-trunc-Prop g
    ( mere-emb-Prop _ _)
    ( λ g' →
      apply-universal-property-trunc-Prop f
        ( mere-emb-Prop _ _)
        ( λ f' → unit-trunc-Prop (comp-emb g' f')))

mere-emb-Large-Preorder : Large-Preorder lsuc (_⊔_)
type-Large-Preorder mere-emb-Large-Preorder l = UU l
leq-prop-Large-Preorder mere-emb-Large-Preorder = mere-emb-Prop
refl-leq-Large-Preorder mere-emb-Large-Preorder = refl-mere-emb
transitive-leq-Large-Preorder mere-emb-Large-Preorder X Y Z =
  transitive-mere-emb
```

### Assuming excluded middle, if there are mere embeddings between `A` and `B` in both directions, then there is a mere equivalence between them

```agda
antisymmetric-mere-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  LEM (l1 ⊔ l2) → mere-emb X Y → mere-emb Y X → mere-equiv X Y
antisymmetric-mere-emb lem f g =
  apply-universal-property-trunc-Prop f
    ( mere-equiv-Prop _ _)
    ( λ f' →
      apply-universal-property-trunc-Prop g
        ( mere-equiv-Prop _ _)
        ( λ g' → unit-trunc-Prop (Cantor-Schröder-Bernstein-Escardó lem f' g')))
```
