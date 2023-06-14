# The interchange law

```agda
module foundation.interchange-law where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

The interchange law shows up in many variations in type theory. The interchange
law for Σ-types is useful in characterizations of identity types; the
interchange law for higher identity types is used in the Eckmann-Hilton argument
to show that the higher homotopy groups of a type are abelian, and the
interchange law for binary operations in rings are useful in computations. We
first define a fully generalized interchange law, and then we specialize it to
make it more directly applicable.

## Definition

### The fully generalized interchange law

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level}
  {A : UU l1} {B : A → UU l2} {C : A → UU l3} {D : (a : A) → B a → C a → UU l4}
  {X1 : UU l5} {Y1 : X1 → UU l6} {X2 : UU l7} {Y2 : X2 → UU l8}
  {Z : UU l9} (R : Z → Z → UU l10)
  (μ1 : (a : A) → B a → X1)
  (μ2 : (a : A) (b : B a) (c : C a) → D a b c → Y1 (μ1 a b))
  (μ3 : (x : X1) → Y1 x → Z)
  (μ4 : (a : A) → C a → X2)
  (μ5 : (a : A) (c : C a) (b : B a) → D a b c → Y2 (μ4 a c))
  (μ6 : (x : X2) → Y2 x → Z)
  where

  fully-generalized-interchange-law : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l10)
  fully-generalized-interchange-law =
    (a : A) (b : B a) (c : C a) (d : D a b c) →
    R (μ3 (μ1 a b) (μ2 a b c d)) (μ6 (μ4 a c) (μ5 a c b d))
```

### The interchange law for two binary operations on a type

```agda
module _
  {l : Level} {X : UU l} (μ : X → X → X)
  where

  interchange-law : (X → X → X) → UU l
  interchange-law ν = (x y u v : X) → μ (ν x y) (ν u v) ＝ ν (μ x u) (μ y v)

  interchange-law-commutative-and-associative :
    ((x y : X) → μ x y ＝ μ y x) → ((x y z : X) → μ (μ x y) z ＝ μ x (μ y z)) →
    interchange-law μ
  interchange-law-commutative-and-associative C A x y u v =
    ( A x y (μ u v)) ∙
    ( ( ap
        ( μ x)
        ( (inv (A y u v)) ∙ ((ap (λ z → μ z v) (C y u)) ∙ (A u y v)))) ∙
      ( inv (A x u (μ y v))))
```
