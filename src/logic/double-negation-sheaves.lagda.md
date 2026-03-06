# Double negation sheaves

```agda
module logic.double-negation-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.double-negation
open import foundation.double-negation-modality
open import foundation.double-negation-stable-propositions
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions

open import logic.de-morgan-types
open import logic.de-morgans-law
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

### The type of double negation stable propositions is a double negation sheaf

```agda
module _
  {l : Level}
  where

  map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop :
    (P : Irrefutable-Prop l) →
    (type-Irrefutable-Prop P → Double-Negation-Stable-Prop l) →
    Double-Negation-Stable-Prop l
  map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop P =
    Π-Double-Negation-Stable-Prop (type-Irrefutable-Prop P)

  compute-map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop :
    (P : Irrefutable-Prop l) →
    (h : type-Irrefutable-Prop P → Double-Negation-Stable-Prop l) →
    (u : type-Irrefutable-Prop P) →
    map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop
      P h ＝
    h u
  compute-map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop
    P h u =
    eq-iff-Double-Negation-Stable-Prop
      ( map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop
        ( P)
        ( h))
      ( h u)
      ( ev u)
      ( λ x v →
        tr
          ( type-Double-Negation-Stable-Prop)
          ( ap h (eq-type-Prop (prop-Irrefutable-Prop P)))
          ( x))

  map-inv-diagonal-type-Double-Negation-Stable-Prop :
    (P : Irrefutable-Prop l) →
    (Q : Double-Negation-Stable-Prop l) →
    ( type-Irrefutable-Prop P → type-Double-Negation-Stable-Prop Q) →
    type-Double-Negation-Stable-Prop Q
  map-inv-diagonal-type-Double-Negation-Stable-Prop P Q h =
    has-double-negation-elim-type-Double-Negation-Stable-Prop Q
      ( λ nQ → is-irrefutable-Irrefutable-Prop P (nQ ∘ h))

  is-double-negation-sheaf-Double-Negation-Stable-Prop :
    is-double-negation-sheaf l (Double-Negation-Stable-Prop l)
  is-double-negation-sheaf-Double-Negation-Stable-Prop P =
    is-equiv-is-invertible
      ( map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop
        ( P))
      ( eq-htpy ∘
        compute-map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop
          ( P))
      ( λ Q →
        eq-iff-Double-Negation-Stable-Prop
          ( map-inv-diagonal-exponential-irrefutable-prop-Double-Negation-Stable-Prop
            ( P)
            ( diagonal-exponential
              ( Double-Negation-Stable-Prop l)
              ( type-Irrefutable-Prop P)
              ( Q)))
          ( Q)
          ( map-inv-diagonal-type-Double-Negation-Stable-Prop P Q)
          ( diagonal-exponential
            ( type-Double-Negation-Stable-Prop Q)
            ( type-Irrefutable-Prop P)))
```

### If the booleans are a double negation sheaf, then propositions are De Morgan

```agda
module _
  {l : Level}
  (is-¬¬-sheaf-bool : is-double-negation-sheaf l bool)
  (P : Prop l)
  where

  point-decision-bool-is-double-negation-sheaf-bool : bool
  point-decision-bool-is-double-negation-sheaf-bool =
    map-inv-is-equiv
      ( is-¬¬-sheaf-bool (is-decidable-prop-Irrefutable-Prop P))
      ( bool-Decidable-Prop ∘ make-Decidable-Prop P)

  compute-point-decision-bool-is-double-negation-sheaf-bool :
    (d : is-decidable-type-Prop P) →
    point-decision-bool-is-double-negation-sheaf-bool ＝
    bool-Decidable-Prop (make-Decidable-Prop P d)
  compute-point-decision-bool-is-double-negation-sheaf-bool =
    htpy-eq
      ( is-section-map-inv-is-equiv
        ( is-¬¬-sheaf-bool (is-decidable-prop-Irrefutable-Prop P))
        ( bool-Decidable-Prop ∘ make-Decidable-Prop P))

  abstract
    is-not-type-Prop-is-false-point-decision-bool-is-double-negation-sheaf-bool :
      point-decision-bool-is-double-negation-sheaf-bool ＝ false →
      ¬ (type-Prop P)
    is-not-type-Prop-is-false-point-decision-bool-is-double-negation-sheaf-bool
      p=false p =
      neq-false-true-bool
        ( ( inv p=false) ∙
          ( compute-point-decision-bool-is-double-negation-sheaf-bool (inl p)))

    is-double-negation-type-Prop-is-not-false-point-decision-bool-is-double-negation-sheaf-bool :
      ¬ (point-decision-bool-is-double-negation-sheaf-bool ＝ false) →
      ¬¬ (type-Prop P)
    is-double-negation-type-Prop-is-not-false-point-decision-bool-is-double-negation-sheaf-bool
      p≠false np =
      p≠false
        ( compute-point-decision-bool-is-double-negation-sheaf-bool (inr np))

    is-de-morgan-type-prop-is-double-negation-sheaf-bool :
      is-de-morgan (type-Prop P)
    is-de-morgan-type-prop-is-double-negation-sheaf-bool =
      map-coproduct
        ( is-not-type-Prop-is-false-point-decision-bool-is-double-negation-sheaf-bool)
        ( is-double-negation-type-Prop-is-not-false-point-decision-bool-is-double-negation-sheaf-bool)
        ( has-decidable-equality-bool
          ( point-decision-bool-is-double-negation-sheaf-bool)
          ( false))
```

### If the booleans are a double negation sheaf, then De Morgan's law holds

```agda
abstract
  de-morgans-law-is-double-negation-sheaf-bool :
    {l1 l2 : Level} →
    is-double-negation-sheaf l1 bool →
    (P : Prop l1) (Q : Prop l2) →
    de-morgans-law P Q
  de-morgans-law-is-double-negation-sheaf-bool is-¬¬-sheaf-bool P Q =
    satisfies-de-morgans-law-is-de-morgan
      ( is-de-morgan-type-prop-is-double-negation-sheaf-bool is-¬¬-sheaf-bool P)
      ( type-Prop Q)

  De-Morgans-Law-Level-is-double-negation-sheaf-bool :
    {l : Level} →
    is-double-negation-sheaf l bool →
    De-Morgans-Law-Level l l
  De-Morgans-Law-Level-is-double-negation-sheaf-bool =
    de-morgans-law-is-double-negation-sheaf-bool
```

## References

{{#bibliography}}
