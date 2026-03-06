# Double negation sheaves

```agda
module orthogonal-factorization-systems.double-negation-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-modality
open import foundation.double-negation-stable-propositions
open import foundation.empty-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import logic.oracle-sheaves

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

{{#concept "Double negation sheaves" Agda=is-double-negation-sheaf}} are types
that are [null](orthogonal-factorization-systems.null-types.md) at
[irrefutable propositions](foundation.irrefutable-propositions.md), i.e.,
[propositions](foundation-core.propositions.md) `P` for which the
[double negation](foundation.double-negation.md) `¬¬P` is true.

Double negation sheaves were first introduced in the context of Homotopy Type
Theory in Example 3.41 of {{#cite RSS20}}, and are considered in the restricted
context of [sets](foundation-core.sets.md) in {{#cite Swan24}}.

## Definitions

### The property of being a double negation sheaf

```agda
is-double-negation-sheaf :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
is-double-negation-sheaf l1 A =
  (P : Irrefutable-Prop l1) → is-null (type-Irrefutable-Prop P) A

is-prop-is-double-negation-sheaf :
  {l1 l2 : Level} {A : UU l2} → is-prop (is-double-negation-sheaf l1 A)
is-prop-is-double-negation-sheaf {A = A} =
  is-prop-Π (λ P → is-prop-is-null (type-Irrefutable-Prop P) A)
```

### The property of being an excluded middle sheaf

```agda
is-excluded-middle-sheaf :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
is-excluded-middle-sheaf l1 {l2} =
  is-oracle-sheaf
    ( excluded-middle-oracle)
    ( excluded-middle-oracle-modality l1 (l1 ⊔ l2))

is-prop-is-excluded-middle-sheaf :
  {l1 l2 : Level} {A : UU l2} → is-prop (is-excluded-middle-sheaf l1 A)
is-prop-is-excluded-middle-sheaf {l1} {l2} {A} =
  is-prop-is-oracle-sheaf
    ( excluded-middle-oracle {l1 ⊔ l2})
    ( excluded-middle-oracle-modality l1 (l1 ⊔ l2))
    ( A)
```

## Properties

### Double negation sheaves and excluded middle sheaves coincide

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  is-double-negation-sheaf-is-excluded-middle-sheaf :
    is-excluded-middle-sheaf l2 A →
    is-double-negation-sheaf l2 A
  is-double-negation-sheaf-is-excluded-middle-sheaf H P =
    H (prop-Irrefutable-Prop P) (is-irrefutable-Irrefutable-Prop P)

  is-excluded-middle-sheaf-is-double-negation-sheaf :
    is-double-negation-sheaf l2 A →
    is-excluded-middle-sheaf l2 A
  is-excluded-middle-sheaf-is-double-negation-sheaf H s t =
    H (make-Irrefutable-Prop s t)

  iff-is-double-negation-sheaf-is-excluded-middle-sheaf :
    is-excluded-middle-sheaf l2 A ↔ is-double-negation-sheaf l2 A
  iff-is-double-negation-sheaf-is-excluded-middle-sheaf =
    ( is-double-negation-sheaf-is-excluded-middle-sheaf ,
      is-excluded-middle-sheaf-is-double-negation-sheaf)
```

### The empty type is a double negation sheaf

```agda
is-double-negation-sheaf-empty :
  {l : Level} → is-double-negation-sheaf l empty
is-double-negation-sheaf-empty P =
  is-equiv-has-converse empty-Prop
    ( hom-Prop (prop-Irrefutable-Prop P) empty-Prop)
    ( is-irrefutable-Irrefutable-Prop P)
```

### Contractible types are double negation sheaves

```agda
is-double-negation-sheaf-is-contr :
  {l1 l2 : Level} {A : UU l1} → is-contr A → is-double-negation-sheaf l2 A
is-double-negation-sheaf-is-contr is-contr-A P =
  is-null-is-contr (type-Irrefutable-Prop P) is-contr-A
```

### Propositions that are double negation sheaves are double negation stable

```agda
module _
  {l : Level} {A : UU l}
  (is-prop-A : is-prop A)
  (is-¬¬-sheaf-A : is-double-negation-sheaf l A)
  where

  compute-is-double-negation-sheaf-is-prop : A ≃ (¬ A → A)
  compute-is-double-negation-sheaf-is-prop =
    ( left-unit-law-product-is-contr
      ( is-proof-irrelevant-is-prop (is-prop-function-type is-prop-A) id)) ∘e
    ( equiv-universal-property-coproduct A) ∘e
    ( _ , is-¬¬-sheaf-A (is-decidable-prop-Irrefutable-Prop (A , is-prop-A)))

  is-double-negation-stable-is-double-negation-sheaf-is-prop :
    is-double-negation-stable (A , is-prop-A)
  is-double-negation-stable-is-double-negation-sheaf-is-prop ¬¬a =
    map-inv-is-equiv (is-¬¬-sheaf-A (A , is-prop-A , ¬¬a)) id
```

### Double negation stable propositions are double negation sheaves

```agda
module _
  {l1 l2 : Level} {A : UU l2}
  (is-prop-A : is-prop A)
  (is-¬¬-stable-A : is-double-negation-stable (A , is-prop-A))
  where

  is-double-negation-sheaf-is-double-negation-stable-is-prop :
    is-double-negation-sheaf l1 A
  is-double-negation-sheaf-is-double-negation-stable-is-prop P =
    is-equiv-has-converse-is-prop
      ( is-prop-A)
      ( is-prop-function-type is-prop-A)
      ( λ f →
        is-¬¬-stable-A
          ( λ na → is-irrefutable-Irrefutable-Prop P (λ p → na (f p))))
```

### The negation of a type is a double negation sheaf

```agda
is-double-negation-sheaf-neg :
  {l1 l2 : Level} {A : UU l2} → is-double-negation-sheaf l1 (¬ A)
is-double-negation-sheaf-neg =
  is-double-negation-sheaf-is-double-negation-stable-is-prop
    ( is-prop-neg)
    ( elim-triple-negation)
```

## References

{{#bibliography}}
