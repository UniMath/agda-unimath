# Inequality on the real numbers

```agda
module real-numbers.inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.complements-subtypes
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.negation-lower-upper-dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The {{#concept "standard ordering" Disambiguation="real numbers" Agda=leq-ℝ}} on
the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
lower cut of one being a subset of the lower cut of the other. This is the
definition used in {{#cite UF13}}, section 11.2.1.

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-ℝ-Prop : Prop (l1 ⊔ l2)
  leq-ℝ-Prop = leq-lower-ℝ-Prop (lower-real-ℝ x) (lower-real-ℝ y)

  leq-ℝ : UU (l1 ⊔ l2)
  leq-ℝ = type-Prop leq-ℝ-Prop
```

## Properties

### Equivalence with inequality on upper cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-ℝ-Prop' : Prop (l1 ⊔ l2)
  leq-ℝ-Prop' = leq-upper-ℝ-Prop (upper-real-ℝ x) (upper-real-ℝ y)

  leq-ℝ' : UU (l1 ⊔ l2)
  leq-ℝ' = type-Prop leq-ℝ-Prop'

  abstract
    leq-iff-ℝ' : leq-ℝ x y ↔ leq-ℝ'
    pr1 leq-iff-ℝ' lx⊆ly q q-in-uy =
      elim-exists
        ( upper-cut-ℝ x q)
        ( λ p (p<q , p≮y) →
          subset-upper-cut-upper-complement-lower-cut-ℝ
            ( x)
            ( q)
            ( intro-exists
              ( p)
              ( p<q ,
                reverses-order-complement-subtype
                  ( lower-cut-ℝ x)
                  ( lower-cut-ℝ y)
                  ( lx⊆ly)
                  ( p)
                  ( p≮y))))
        ( subset-upper-complement-lower-cut-upper-cut-ℝ y q q-in-uy)
    pr2 leq-iff-ℝ' uy⊆ux p p-in-lx =
      elim-exists
        ( lower-cut-ℝ y p)
        ( λ q (p<q , x≮q) →
          subset-lower-cut-lower-complement-upper-cut-ℝ
            ( y)
            ( p)
            ( intro-exists
              ( q)
              ( p<q ,
                reverses-order-complement-subtype
                  ( upper-cut-ℝ y)
                  ( upper-cut-ℝ x)
                  ( uy⊆ux)
                  ( q)
                  ( x≮q))))
        ( subset-lower-complement-upper-cut-lower-cut-ℝ x p p-in-lx)
```

### Inequality on the real numbers is reflexive

```agda
refl-leq-ℝ : {l : Level} → (x : ℝ l) → leq-ℝ x x
refl-leq-ℝ x = refl-leq-Large-Preorder lower-ℝ-Large-Preorder (lower-real-ℝ x)
```

### Inequality on the real numbers is antisymmetric

```agda
antisymmetric-leq-ℝ : {l : Level} → (x y : ℝ l) → leq-ℝ x y → leq-ℝ y x → x ＝ y
antisymmetric-leq-ℝ x y x≤y y≤x =
  eq-eq-lower-cut-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) x≤y y≤x)
```

### Inequality on the real numbers is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  transitive-leq-ℝ : leq-ℝ y z → leq-ℝ x y → leq-ℝ x z
  transitive-leq-ℝ =
    transitive-leq-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) (lower-cut-ℝ z)
```

### The large preorder of real numbers

```agda
ℝ-Large-Preorder : Large-Preorder lsuc _⊔_
type-Large-Preorder ℝ-Large-Preorder = ℝ
leq-prop-Large-Preorder ℝ-Large-Preorder = leq-ℝ-Prop
refl-leq-Large-Preorder ℝ-Large-Preorder = refl-leq-ℝ
transitive-leq-Large-Preorder ℝ-Large-Preorder = transitive-leq-ℝ
```

### The large poset of real numbers

```agda
ℝ-Large-Poset : Large-Poset lsuc _⊔_
large-preorder-Large-Poset ℝ-Large-Poset = ℝ-Large-Preorder
antisymmetric-leq-Large-Poset ℝ-Large-Poset = antisymmetric-leq-ℝ
```

### The partially ordered set of reals at a specific level

```agda
ℝ-Preorder : (l : Level) → Preorder (lsuc l) l
ℝ-Preorder = preorder-Large-Preorder ℝ-Large-Preorder

ℝ-Poset : (l : Level) → Poset (lsuc l) l
ℝ-Poset = poset-Large-Poset ℝ-Large-Poset
```

### The canonical map from rational numbers to the reals preserves and reflects inequality

```agda
preserves-leq-real-ℚ : (x y : ℚ) → leq-ℚ x y → leq-ℝ (real-ℚ x) (real-ℚ y)
preserves-leq-real-ℚ = preserves-leq-lower-real-ℚ

reflects-leq-real-ℚ : (x y : ℚ) → leq-ℝ (real-ℚ x) (real-ℚ y) → leq-ℚ x y
reflects-leq-real-ℚ = reflects-leq-lower-real-ℚ

iff-leq-real-ℚ : (x y : ℚ) → leq-ℚ x y ↔ leq-ℝ (real-ℚ x) (real-ℚ y)
iff-leq-real-ℚ = iff-leq-lower-real-ℚ
```

### Negation reverses inequality on the real numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  neg-leq-ℝ : leq-ℝ x y → leq-ℝ (neg-ℝ y) (neg-ℝ x)
  neg-leq-ℝ x≤y =
    backward-implication
      ( leq-iff-ℝ' (neg-ℝ y) (neg-ℝ x))
      ( λ q → x≤y (neg-ℚ q))
```

## References

{{#bibliography}}
