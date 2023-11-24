# Mere equivalences of concrete group actions

```agda
module group-theory.mere-equivalences-concrete-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.functoriality-propositional-truncation
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-group-actions
```

</details>

## Definition

```agda
mere-equiv-prop-action-Concrete-Group :
  {l1 l2 l3 : Level} (G : Concrete-Group l1) →
  action-Concrete-Group l2 G → action-Concrete-Group l3 G →
  Prop (l1 ⊔ l2 ⊔ l3)
mere-equiv-prop-action-Concrete-Group G X Y =
  trunc-Prop (equiv-action-Concrete-Group G X Y)

mere-equiv-action-Concrete-Group :
  {l1 l2 l3 : Level} (G : Concrete-Group l1) →
  action-Concrete-Group l2 G → action-Concrete-Group l3 G → UU (l1 ⊔ l2 ⊔ l3)
mere-equiv-action-Concrete-Group G X Y =
  type-Prop (mere-equiv-prop-action-Concrete-Group G X Y)

is-prop-mere-equiv-action-Concrete-Group :
  {l1 l2 l3 : Level} (G : Concrete-Group l1)
  (X : action-Concrete-Group l2 G) (Y : action-Concrete-Group l3 G) →
  is-prop (mere-equiv-action-Concrete-Group G X Y)
is-prop-mere-equiv-action-Concrete-Group G X Y =
  is-prop-type-Prop (mere-equiv-prop-action-Concrete-Group G X Y)

refl-mere-equiv-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  mere-equiv-action-Concrete-Group G X X
refl-mere-equiv-action-Concrete-Group G X =
  unit-trunc-Prop (id-equiv-action-Concrete-Group G X)
```

## Properties

### Mere equivalences of concrete group actions give mere equalities

```agda
mere-eq-mere-equiv-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1)
  (X : action-Concrete-Group l2 G) (Y : action-Concrete-Group l2 G) →
  mere-equiv-action-Concrete-Group G X Y →
  mere-eq X Y
mere-eq-mere-equiv-action-Concrete-Group G X Y =
  map-trunc-Prop (eq-equiv-action-Concrete-Group G X Y)
```
