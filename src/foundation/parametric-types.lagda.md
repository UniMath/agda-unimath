# Parametric types

```agda
module foundation.parametric-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.double-negation
open import foundation.double-negation-stable-propositions
open import foundation.embeddings
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.negated-equality
open import foundation.propositional-maps
open import foundation.retracts-of-types
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-empty-type
open import foundation.types-with-decidable-dependent-product-types
open import foundation.types-with-decidable-universal-quantifications
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

A type `X : 𝒰` is
{{#concept "parametric" Disambiguation="type" Agda=is-parametric Agda=Parametric-Type}}
if the [constant map](foundation.constant-maps.md) `X → (𝒰 → X)` is an
[equivalence](foundation-core.equivalences.md). In other words, if `X` is
`𝒰`-[null](orthogonal-factorization-systems.null-types.md).

## Definitions

### The predicate on a type of being parametric

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-parametric : UU (l1 ⊔ lsuc l2)
  is-parametric = is-null (UU l2) X

  is-prop-is-parametric : is-prop is-parametric
  is-prop-is-parametric = is-prop-is-null (UU l2) X

  is-parametric-Prop : Prop (l1 ⊔ lsuc l2)
  is-parametric-Prop = is-null-Prop (UU l2) X
```

### The universe of parametric types

```agda
Parametric-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Parametric-Type l1 l2 = Σ (UU l1) (is-parametric l2)

module _
  {l1 l2 : Level} (X : Parametric-Type l1 l2)
  where

  type-Parametric-Type : UU l1
  type-Parametric-Type = pr1 X

  is-parametric-type-Parametric-Type :
    is-parametric l2 type-Parametric-Type
  is-parametric-type-Parametric-Type = pr2 X
```

## Properties

### Contractible types are parametric

```agda
abstract
  is-parametric-is-contr :
    {l1 l2 : Level} {X : UU l1} →
    is-contr X → is-parametric l2 X
  is-parametric-is-contr {l2 = l2} =
    is-null-is-contr (UU l2)
```

### The unit type is parametric

```agda
abstract
  is-parametric-unit :
    {l : Level} → is-parametric l unit
  is-parametric-unit {l} =
    is-parametric-is-contr is-contr-unit
```

### The empty type is parametric

```agda
abstract
  is-parametric-empty :
    {l : Level} → is-parametric l empty
  is-parametric-empty {l} =
    is-equiv-is-empty _ (ev (raise-empty l))
```

### Propositions are parametric

```agda
abstract
  is-parametric-is-prop :
    {l1 l2 : Level} {X : UU l1} →
    is-prop X → is-parametric l2 X
  is-parametric-is-prop {l1} {l2} H =
    is-null-is-prop H (ev (raise-empty l2))
```

### Parametric types are closed under equivalences

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where abstract

  is-parametric-equiv :
    X ≃ Y → is-parametric l3 Y → is-parametric l3 X
  is-parametric-equiv = is-null-equiv-base

  is-parametric-equiv' :
    X ≃ Y → is-parametric l3 X → is-parametric l3 Y
  is-parametric-equiv' = is-null-equiv-base ∘ inv-equiv
```

### Parametric types are closed under retracts

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where abstract

  is-parametric-retract :
    X retract-of Y → is-parametric l3 Y → is-parametric l3 X
  is-parametric-retract = is-null-retract-base
```

### Parametric types are closed under embeddings

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where abstract

  is-parametric-emb :
    Y ↪ X → is-parametric l3 X → is-parametric l3 Y
  is-parametric-emb e is-parametric-X =
    is-parametric-equiv'
      ( equiv-total-fiber (map-emb e))
      ( is-null-Σ
        ( is-parametric-X)
        ( λ x → is-parametric-is-prop (is-prop-type-Prop (fiber-emb-Prop e x))))
```

### If there is a type that refutes decidable universal quantifications, then discrete types are parametric

Given a discrete type `B`, if there exists a function `f : I → B` together with
elements `X` and `Y` of `I` such that `f X ≠ f Y`, and moreover there is some
assignment `χ` of double negation stable propositions to `I` that sends true
propositions to `X` and false propositions to `Y`, then every type has decidable
universal quantifications. For `I` equal to a universe, there is such a map
given by splitting at any given double negation stable proposition:

```text
  χ P ≔ (P × X) + ((¬ P) × Y)
```

Therefore, if some type does not have decidable universal quantifications, then
`f` must send `X` and `Y` to the same element in `B`.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1}
  (B : Discrete-Type l2)
  (f : I → type-Discrete-Type B)
  {X Y : I}
  (fX≠fY : f X ≠ f Y)
  (χ : Double-Negation-Stable-Prop l3 → I)
  (eq-χ-true :
    (P : Double-Negation-Stable-Prop l3) →
    type-Double-Negation-Stable-Prop P →
    χ P ＝ X)
  (eq-χ-false :
    (P : Double-Negation-Stable-Prop l3) →
    ¬ type-Double-Negation-Stable-Prop P →
    χ P ＝ Y)
  where abstract

  is-decidable-split-on-double-negation-stable-prop-Discrete-Type :
    (P : Double-Negation-Stable-Prop l3) →
    is-decidable (type-Double-Negation-Stable-Prop P)
  is-decidable-split-on-double-negation-stable-prop-Discrete-Type P =
    map-coproduct
      ( λ p →
        has-double-negation-elim-type-Double-Negation-Stable-Prop P
          ( λ np → fX≠fY (inv p ∙ ap f (eq-χ-false P np))))
      ( λ np p → np (ap f (eq-χ-true P p)))
      ( has-decidable-equality-type-Discrete-Type B (f (χ P)) (f X))

  has-decidable-∀-has-separating-map-split-Discrete-Type :
    (A : UU l3) → has-decidable-∀-Level l3 A
  has-decidable-∀-has-separating-map-split-Discrete-Type A P =
    is-decidable-split-on-double-negation-stable-prop-Discrete-Type
      ( is-full-decidable-subtype P ,
        ( is-prop-type-Prop (is-full-decidable-subtype-Prop P) ,
          λ nn-all-P a →
          double-negation-elim-is-decidable
            ( is-decidable-decidable-subtype P a)
            ( λ nn-Pa → nn-all-P (λ all-P → nn-Pa (all-P a)))))

abstract
  separate-map-split-on-prop¬¬-not-has-decidable-∀-Level-Discrete-Type :
    {l1 l2 l3 : Level} {A : UU l1} {I : UU l2} →
    ¬ has-decidable-∀-Level l1 A →
    (B : Discrete-Type l3)
    (f : I → type-Discrete-Type B)
    {X Y : I}
    (χ : (f X ≠ f Y) → Double-Negation-Stable-Prop l1 → I) →
    ( (fX≠fY : f X ≠ f Y) (P : Double-Negation-Stable-Prop l1) →
      type-Double-Negation-Stable-Prop P → χ fX≠fY P ＝ X) →
    ( (fX≠fY : f X ≠ f Y) (P : Double-Negation-Stable-Prop l1) →
      ¬ type-Double-Negation-Stable-Prop P → χ fX≠fY P ＝ Y) →
    f X ＝ f Y
  separate-map-split-on-prop¬¬-not-has-decidable-∀-Level-Discrete-Type
    {A = A} ¬d∀A B f {X} {Y} χ eq-χ-true eq-χ-false =
    rec-coproduct
      ( id)
      ( λ fX≠fY →
        ex-falso
          ( ¬d∀A
            ( has-decidable-∀-has-separating-map-split-Discrete-Type
              ( B)
              ( f)
              ( fX≠fY)
              ( χ fX≠fY)
              ( eq-χ-true fX≠fY)
              ( eq-χ-false fX≠fY)
              ( A))))
      ( has-decidable-equality-type-Discrete-Type B (f X) (f Y))

module _
  {l1 l2 l3 : Level} (P'@(P , is-prop-P) : Prop l1) {X : UU l2} {Y : UU l3}
  where

  compute-split-on-prop¬¬-true-parametric-types :
    P → ((P × X) + ((¬ P) × Y)) ≃ X
  compute-split-on-prop¬¬-true-parametric-types p =
    ( left-unit-law-product-is-contr
      ( is-proof-irrelevant-is-prop is-prop-P p)) ∘e
    ( right-unit-law-coproduct-is-empty (P × X) ((¬ P) × Y) (λ z → (pr1 z) p))

  compute-split-on-prop¬¬-false-parametric-types :
    ¬ P → ((P × X) + ((¬ P) × Y)) ≃ Y
  compute-split-on-prop¬¬-false-parametric-types np =
    ( left-unit-law-product-is-contr
      ( is-proof-irrelevant-is-prop is-property-is-empty np)) ∘e
    ( left-unit-law-coproduct-is-empty (P × X) ((¬ P) × Y) (np ∘ pr1))

split-on-double-negation-stable-prop-Discrete-Type :
  {l1 l2 : Level} (B : Discrete-Type l2) →
  (f : UU l1 → type-Discrete-Type B) {X Y : UU l1} →
  Double-Negation-Stable-Prop l1 → UU l1
split-on-double-negation-stable-prop-Discrete-Type B f {X} {Y} P =
  ( type-Double-Negation-Stable-Prop P × X) +
  ((¬ type-Double-Negation-Stable-Prop P) × Y)

module _
  {l1 l2 : Level} {A : UU l1}
  (¬d∀A : ¬ has-decidable-∀-Level l1 A)
  (B : Discrete-Type l2)
  where abstract

  rice-contrapositive-not-has-decidable-∀-Discrete-Type :
    (f : UU l1 → type-Discrete-Type B) →
    (X Y : UU l1) → f X ＝ f Y
  rice-contrapositive-not-has-decidable-∀-Discrete-Type f X Y =
    separate-map-split-on-prop¬¬-not-has-decidable-∀-Level-Discrete-Type
      ( ¬d∀A)
      ( B)
      ( f)
      ( λ _ → split-on-double-negation-stable-prop-Discrete-Type B f)
      ( λ _ P p →
        eq-equiv
          ( compute-split-on-prop¬¬-true-parametric-types
            ( prop-Double-Negation-Stable-Prop P)
            ( p)))
      ( λ _ P np →
        eq-equiv
          ( compute-split-on-prop¬¬-false-parametric-types
            ( prop-Double-Negation-Stable-Prop P)
            ( np)))

  is-parametric-not-has-decidable-∀-Discrete-Type :
    is-parametric l1 (type-Discrete-Type B)
  is-parametric-not-has-decidable-∀-Discrete-Type =
    is-equiv-is-invertible
      ( ev (raise-empty l1))
      ( λ f →
        eq-htpy
          ( rice-contrapositive-not-has-decidable-∀-Discrete-Type f
            ( raise-empty l1)))
      ( refl-htpy)
```

### If the weak limited principle of omniscience is refuted, then discrete types are parametric

```agda
is-parametric-lzero-not-WLPO-Discrete-Type :
  {l : Level} →
  ¬ level-WLPO lzero →
  (B : Discrete-Type l) →
  is-parametric lzero (type-Discrete-Type B)
is-parametric-lzero-not-WLPO-Discrete-Type =
  is-parametric-not-has-decidable-∀-Discrete-Type
```

This result could be made fully universe polymorphic with some extra universe
raising infrastructure.

## See also

- [Subuniverse-parametric types](foundation.subuniverse-parametric-types.md)
- [The parametricity axiom](foundation.parametricity-axiom.md)
