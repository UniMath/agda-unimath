# The decidable total order of natural numbers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.decidable-total-order-natural-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.propositional-truncations funext univalence
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.decidable-total-orders funext univalence truncations
open import order-theory.order-preserving-maps-posets funext univalence truncations
open import order-theory.order-preserving-maps-preorders funext univalence truncations
open import order-theory.posets funext univalence truncations
open import order-theory.preorders funext univalence truncations
open import order-theory.total-orders funext univalence truncations
```

</details>

## Idea

The type of [natural numbers](elementary-number-theory.natural-numbers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-natural-numbers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definition

```agda
is-total-leq-ℕ : is-total-Poset ℕ-Poset
is-total-leq-ℕ n m = unit-trunc-Prop (linear-leq-ℕ n m)

ℕ-Total-Order : Total-Order lzero lzero
pr1 ℕ-Total-Order = ℕ-Poset
pr2 ℕ-Total-Order = is-total-leq-ℕ

ℕ-Decidable-Total-Order : Decidable-Total-Order lzero lzero
pr1 ℕ-Decidable-Total-Order = ℕ-Poset
pr1 (pr2 ℕ-Decidable-Total-Order) = is-total-leq-ℕ
pr2 (pr2 ℕ-Decidable-Total-Order) = is-decidable-leq-ℕ
```

## Properties

### Maps out of the natural numbers that preserve order by induction

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  preserves-order-ind-ℕ-Preorder :
    (f : ℕ → type-Preorder P) →
    ((n : ℕ) → leq-Preorder P (f n) (f (succ-ℕ n))) →
    preserves-order-Preorder ℕ-Preorder P f
  preserves-order-ind-ℕ-Preorder f H zero-ℕ zero-ℕ p =
    refl-leq-Preorder P (f zero-ℕ)
  preserves-order-ind-ℕ-Preorder f H zero-ℕ (succ-ℕ m) p =
    transitive-leq-Preorder P (f 0) (f m) (f (succ-ℕ m))
      ( H m)
      ( preserves-order-ind-ℕ-Preorder f H zero-ℕ m star)
  preserves-order-ind-ℕ-Preorder f H (succ-ℕ n) zero-ℕ ()
  preserves-order-ind-ℕ-Preorder f H (succ-ℕ n) (succ-ℕ m) =
    preserves-order-ind-ℕ-Preorder (f ∘ succ-ℕ) (H ∘ succ-ℕ) n m

  hom-ind-ℕ-Preorder :
    (f : ℕ → type-Preorder P) →
    ((n : ℕ) → leq-Preorder P (f n) (f (succ-ℕ n))) →
    hom-Preorder (ℕ-Preorder) P
  hom-ind-ℕ-Preorder f H = f , preserves-order-ind-ℕ-Preorder f H

module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  preserves-order-ind-ℕ-Poset :
    (f : ℕ → type-Poset P) →
    ((n : ℕ) → leq-Poset P (f n) (f (succ-ℕ n))) →
    preserves-order-Poset ℕ-Poset P f
  preserves-order-ind-ℕ-Poset =
    preserves-order-ind-ℕ-Preorder (preorder-Poset P)

  hom-ind-ℕ-Poset :
    (f : ℕ → type-Poset P) →
    ((n : ℕ) → leq-Poset P (f n) (f (succ-ℕ n))) →
    hom-Poset (ℕ-Poset) P
  hom-ind-ℕ-Poset = hom-ind-ℕ-Preorder (preorder-Poset P)
```
