# The poset of premetric structures on a type

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module metric-spaces.ordering-premetric-structures
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers funext univalence truncations

open import foundation.binary-relations funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import metric-spaces.premetric-structures funext univalence truncations

open import order-theory.posets funext univalence truncations
open import order-theory.preorders funext univalence truncations
```

</details>

## Idea

A [premetric structure](metric-spaces.premetric-structures.md) `U` on a type `A`
is {{#concept "finer" Disambiguation="premetric on a type" Agda=leq-Premetric}}
than another premetric `V` if `(U d)`-neighborhoods are `(V d)`-neighborhoods
for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `d`,
i.e., if any upper bound on the distance between two points in `U` also bounds
their distance in `V`. This is a [partial order](order-theory.posets.md) on the
type of premetric structures on `A`.

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U V : Premetric l2 A)
  where

  leq-prop-Premetric : Prop (l1 ⊔ l2)
  leq-prop-Premetric =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y → hom-Prop (U d x y) (V d x y))))

  leq-Premetric : UU (l1 ⊔ l2)
  leq-Premetric = type-Prop leq-prop-Premetric

  is-prop-leq-Premetric : is-prop leq-Premetric
  is-prop-leq-Premetric = is-prop-type-Prop leq-prop-Premetric
```

## Properties

### The ordering on premetric structures is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U : Premetric l2 A)
  where

  refl-leq-Premetric : leq-Premetric U U
  refl-leq-Premetric d x y H = H

  leq-eq-Premetric : (V : Premetric l2 A) → (U ＝ V) → leq-Premetric U V
  leq-eq-Premetric .U refl = refl-leq-Premetric
```

### The ordering on premetric structures is transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U V W : Premetric l2 A)
  where

  transitive-leq-Premetric :
    leq-Premetric V W → leq-Premetric U V → leq-Premetric U W
  transitive-leq-Premetric H K d x y = H d x y ∘ K d x y
```

### The ordering on premetric structures is antisymmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U V : Premetric l2 A)
  where

  antisymmetric-leq-Premetric :
    leq-Premetric U V → leq-Premetric V U → U ＝ V
  antisymmetric-leq-Premetric I J =
    eq-Eq-Premetric
      ( U)
      ( V)
      ( λ d x y → (I d x y , J d x y))
```

### The poset of premetric structures on a type

```agda
module _
  {l1 l2 : Level} (A : UU l1)
  where

  preorder-Premetric : Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 preorder-Premetric = Premetric l2 A
  pr2 preorder-Premetric =
    leq-prop-Premetric , refl-leq-Premetric , transitive-leq-Premetric

  poset-Premetric : Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  poset-Premetric = preorder-Premetric , antisymmetric-leq-Premetric
```
