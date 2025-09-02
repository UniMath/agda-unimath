# Inequality on the real numbers

```agda
module real-numbers.inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.complements-subtypes
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.negation-lower-upper-dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
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

infix 30 _≤-ℝ_
_≤-ℝ_ = leq-ℝ
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
    leq'-leq-ℝ : leq-ℝ x y → leq-ℝ'
    leq'-leq-ℝ lx⊆ly q y<q =
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
        ( subset-upper-complement-lower-cut-upper-cut-ℝ y q y<q)

    leq-leq'-ℝ : leq-ℝ' → leq-ℝ x y
    leq-leq'-ℝ uy⊆ux p p<x =
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
        ( subset-lower-complement-upper-cut-lower-cut-ℝ x p p<x)

    leq-iff-ℝ' : leq-ℝ x y ↔ leq-ℝ'
    leq-iff-ℝ' = (leq'-leq-ℝ , leq-leq'-ℝ)
```

### Inequality on the real numbers is reflexive

```agda
abstract
  refl-leq-ℝ : {l : Level} → (x : ℝ l) → leq-ℝ x x
  refl-leq-ℝ x = refl-leq-Large-Preorder lower-ℝ-Large-Preorder (lower-real-ℝ x)

  leq-eq-ℝ : {l : Level} → (x y : ℝ l) → x ＝ y → leq-ℝ x y
  leq-eq-ℝ x y x=y = tr (leq-ℝ x) x=y (refl-leq-ℝ x)

opaque
  unfolding sim-prop-ℝ

  leq-sim-ℝ : {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → sim-ℝ x y → leq-ℝ x y
  leq-sim-ℝ _ _ = pr1
```

### Inequality on the real numbers is antisymmetric

```agda
opaque
  unfolding sim-prop-ℝ

  sim-antisymmetric-leq-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → leq-ℝ x y → leq-ℝ y x → sim-ℝ x y
  sim-antisymmetric-leq-ℝ _ _ = pair

  antisymmetric-leq-ℝ :
    {l : Level} → (x y : ℝ l) → leq-ℝ x y → leq-ℝ y x → x ＝ y
  antisymmetric-leq-ℝ x y x≤y y≤x =
    eq-sim-ℝ (sim-antisymmetric-leq-ℝ x y x≤y y≤x)
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

### Similarity in the large poset of real numbers is equivalent to similarity

```agda
opaque
  unfolding sim-prop-ℝ

  sim-sim-leq-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-Large-Poset ℝ-Large-Poset x y → sim-ℝ x y
  sim-sim-leq-ℝ = id

  sim-leq-sim-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-ℝ x y → sim-Large-Poset ℝ-Large-Poset x y
  sim-leq-sim-ℝ = id

  sim-iff-sim-leq-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-ℝ x y ↔ sim-Large-Poset ℝ-Large-Poset x y
  sim-iff-sim-leq-ℝ = id-iff
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
  neg-leq-ℝ x≤y = leq-leq'-ℝ (neg-ℝ y) (neg-ℝ x) (x≤y ∘ neg-ℚ)
```

### Inequality on the real numbers is invariant under similarity

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) (x~y : sim-ℝ x y)
  where

  opaque
    unfolding sim-prop-ℝ

    preserves-leq-left-sim-ℝ : leq-ℝ x z → leq-ℝ y z
    preserves-leq-left-sim-ℝ x≤z q q<y = x≤z q (pr2 x~y q q<y)

    preserves-leq-right-sim-ℝ : leq-ℝ z x → leq-ℝ z y
    preserves-leq-right-sim-ℝ z≤x q q<z = pr1 x~y q (z≤x q q<z)

module _
  {l1 l2 l3 l4 : Level}
  (x1 : ℝ l1) (x2 : ℝ l2) (y1 : ℝ l3) (y2 : ℝ l4)
  (x1~x2 : sim-ℝ x1 x2) (y1~y2 : sim-ℝ y1 y2)
  where

  preserves-leq-sim-ℝ : leq-ℝ x1 y1 → leq-ℝ x2 y2
  preserves-leq-sim-ℝ x1≤y1 =
    preserves-leq-left-sim-ℝ
      ( y2)
      ( x1)
      ( x2)
      ( x1~x2)
      ( preserves-leq-right-sim-ℝ x1 y1 y2 y1~y2 x1≤y1)
```

### Inequality on the real numbers is translation invariant

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  opaque
    unfolding add-ℝ

    preserves-leq-right-add-ℝ : leq-ℝ x y → leq-ℝ (x +ℝ z) (y +ℝ z)
    preserves-leq-right-add-ℝ x≤y _ =
      map-tot-exists (λ (qx , _) → map-product (x≤y qx) id)

    preserves-leq-left-add-ℝ : leq-ℝ x y → leq-ℝ (z +ℝ x) (z +ℝ y)
    preserves-leq-left-add-ℝ x≤y _ =
      map-tot-exists (λ (_ , qx) → map-product id (map-product (x≤y qx) id))

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  abstract
    reflects-leq-right-add-ℝ : leq-ℝ (x +ℝ z) (y +ℝ z) → leq-ℝ x y
    reflects-leq-right-add-ℝ x+z≤y+z =
      preserves-leq-sim-ℝ
        ( (x +ℝ z) -ℝ z)
        ( x)
        ( (y +ℝ z) -ℝ z)
        ( y)
        ( cancel-right-add-diff-ℝ x z)
        ( cancel-right-add-diff-ℝ y z)
        ( preserves-leq-right-add-ℝ (neg-ℝ z) (x +ℝ z) (y +ℝ z) x+z≤y+z)

    reflects-leq-left-add-ℝ : leq-ℝ (z +ℝ x) (z +ℝ y) → leq-ℝ x y
    reflects-leq-left-add-ℝ z+x≤z+y =
      reflects-leq-right-add-ℝ
        ( binary-tr
          ( leq-ℝ)
          ( commutative-add-ℝ z x)
          ( commutative-add-ℝ z y)
          ( z+x≤z+y))

module _
  {l1 l2 l3 : Level} (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  iff-translate-right-leq-ℝ : leq-ℝ x y ↔ leq-ℝ (x +ℝ z) (y +ℝ z)
  pr1 iff-translate-right-leq-ℝ = preserves-leq-right-add-ℝ z x y
  pr2 iff-translate-right-leq-ℝ = reflects-leq-right-add-ℝ z x y

  iff-translate-left-leq-ℝ : leq-ℝ x y ↔ leq-ℝ (z +ℝ x) (z +ℝ y)
  pr1 iff-translate-left-leq-ℝ = preserves-leq-left-add-ℝ z x y
  pr2 iff-translate-left-leq-ℝ = reflects-leq-left-add-ℝ z x y

abstract
  preserves-leq-add-ℝ :
    {l1 l2 l3 l4 : Level} (a : ℝ l1) (b : ℝ l2) (c : ℝ l3) (d : ℝ l4) →
    leq-ℝ a b → leq-ℝ c d → leq-ℝ (a +ℝ c) (b +ℝ d)
  preserves-leq-add-ℝ a b c d a≤b c≤d =
    transitive-leq-ℝ
      ( a +ℝ c)
      ( a +ℝ d)
      ( b +ℝ d)
      ( preserves-leq-right-add-ℝ d a b a≤b)
      ( preserves-leq-left-add-ℝ a c d c≤d)
```

### Transposition laws

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  abstract
    leq-transpose-left-diff-ℝ : leq-ℝ (x -ℝ y) z → leq-ℝ x (z +ℝ y)
    leq-transpose-left-diff-ℝ x-y≤z =
      preserves-leq-left-sim-ℝ
        ( z +ℝ y)
        ( (x -ℝ y) +ℝ y)
        ( x)
        ( cancel-right-diff-add-ℝ x y)
        ( preserves-leq-right-add-ℝ y (x -ℝ y) z x-y≤z)

    leq-transpose-left-add-ℝ : leq-ℝ (x +ℝ y) z → leq-ℝ x (z -ℝ y)
    leq-transpose-left-add-ℝ x+y≤z =
      preserves-leq-left-sim-ℝ
        (z -ℝ y)
        ( (x +ℝ y) -ℝ y)
        ( x)
        ( cancel-right-add-diff-ℝ x y)
        ( preserves-leq-right-add-ℝ (neg-ℝ y) (x +ℝ y) z x+y≤z)

    leq-transpose-right-add-ℝ : leq-ℝ x (y +ℝ z) → leq-ℝ (x -ℝ z) y
    leq-transpose-right-add-ℝ x≤y+z =
      preserves-leq-right-sim-ℝ
        ( x -ℝ z)
        ( (y +ℝ z) -ℝ z)
        ( y)
        ( cancel-right-add-diff-ℝ y z)
        ( preserves-leq-right-add-ℝ (neg-ℝ z) x (y +ℝ z) x≤y+z)

    leq-transpose-right-diff-ℝ : leq-ℝ x (y -ℝ z) → leq-ℝ (x +ℝ z) y
    leq-transpose-right-diff-ℝ x≤y-z =
      preserves-leq-right-sim-ℝ
        ( x +ℝ z)
        ( (y -ℝ z) +ℝ z)
        ( y)
        ( cancel-right-diff-add-ℝ y z)
        ( preserves-leq-right-add-ℝ z x (y -ℝ z) x≤y-z)
```

### Swapping laws

```agda
abstract
  swap-right-diff-leq-ℝ :
    {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3) →
    leq-ℝ (x -ℝ y) z → leq-ℝ (x -ℝ z) y
  swap-right-diff-leq-ℝ x y z x-y≤z =
    leq-transpose-right-add-ℝ
      ( x)
      ( y)
      ( z)
      ( tr
        ( leq-ℝ x)
        ( commutative-add-ℝ _ _)
        ( leq-transpose-left-diff-ℝ x y z x-y≤z))
```

### Addition of real numbers preserves lower neighborhoods

```agda
module _
  {l1 l2 l3 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  preserves-lower-neighborhood-leq-left-add-ℝ :
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ
      ( add-ℝ x y)
      ( (add-ℝ x z) +ℝ real-ℚ (rational-ℚ⁺ d))
  preserves-lower-neighborhood-leq-left-add-ℝ z≤y+d =
    inv-tr
      ( leq-ℝ (x +ℝ y))
      ( associative-add-ℝ x z (real-ℚ (rational-ℚ⁺ d)))
      ( preserves-leq-left-add-ℝ
        ( x)
        ( y)
        ( z +ℝ real-ℚ (rational-ℚ⁺ d))
        ( z≤y+d))

  preserves-lower-neighborhood-leq-right-add-ℝ :
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ
      ( add-ℝ y x)
      ( (add-ℝ z x) +ℝ real-ℚ (rational-ℚ⁺ d))
  preserves-lower-neighborhood-leq-right-add-ℝ z≤y+d =
    binary-tr
      ( λ u v → leq-ℝ u (v +ℝ real-ℚ (rational-ℚ⁺ d)))
      ( commutative-add-ℝ x y)
      ( commutative-add-ℝ x z)
      ( preserves-lower-neighborhood-leq-left-add-ℝ z≤y+d)
```

### Addition of real numbers reflects lower neighborhoods

```agda
module _
  {l1 l2 l3 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  reflects-lower-neighborhood-leq-left-add-ℝ :
    leq-ℝ
      ( add-ℝ x y)
      ( (add-ℝ x z) +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d))
  reflects-lower-neighborhood-leq-left-add-ℝ x+y≤x+z+d =
    reflects-leq-left-add-ℝ
      ( x)
      ( y)
      ( z +ℝ real-ℚ (rational-ℚ⁺ d))
      ( tr
        ( leq-ℝ (x +ℝ y))
        ( associative-add-ℝ x z (real-ℚ (rational-ℚ⁺ d)))
        ( x+y≤x+z+d))

  reflects-lower-neighborhood-leq-right-add-ℝ :
    leq-ℝ
      ( add-ℝ y x)
      ( (add-ℝ z x) +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d))
  reflects-lower-neighborhood-leq-right-add-ℝ y+x≤z+y+d =
    reflects-lower-neighborhood-leq-left-add-ℝ
      ( binary-tr
        ( λ u v → leq-ℝ u (v +ℝ real-ℚ (rational-ℚ⁺ d)))
        ( commutative-add-ℝ y x)
        ( commutative-add-ℝ z x)
        ( y+x≤z+y+d))
```

### Negation of real numbers reverses lower neighborhoods

```agda
module _
  {l1 l2 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2)
  where

  reverses-lower-neighborhood-neg-ℝ :
    leq-ℝ x (y +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ (neg-ℝ y) (neg-ℝ x +ℝ real-ℚ (rational-ℚ⁺ d))
  reverses-lower-neighborhood-neg-ℝ x≤y+d =
    tr
      ( leq-ℝ (neg-ℝ y))
      ( ( distributive-neg-add-ℝ x ((neg-ℝ ∘ real-ℚ ∘ rational-ℚ⁺) d)) ∙
        ( ap (add-ℝ (neg-ℝ x)) (neg-neg-ℝ (real-ℚ (rational-ℚ⁺ d)))))
      ( neg-leq-ℝ
        ( x -ℝ real-ℚ (rational-ℚ⁺ d))
        ( y)
        ( leq-transpose-right-add-ℝ
          ( x)
          ( y)
          ( real-ℚ (rational-ℚ⁺ d))
          ( x≤y+d)))
```

## References

{{#bibliography}}
