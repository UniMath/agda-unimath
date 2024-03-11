# Joins of types

```agda
module synthetic-homotopy-theory.joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.span-diagrams
open import foundation.spans
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.action-functions-cocones-under-span-diagrams
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **join** of `A` and `B` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the
[span diagram](foundation.span-diagrams.md) `A ← A × B → B`.

## Definitions

### The defining span diagram of the join

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  domain-span-diagram-join : UU l1
  domain-span-diagram-join = A

  codomain-span-diagram-join : UU l2
  codomain-span-diagram-join = B

  spanning-type-span-diagram-join : UU (l1 ⊔ l2)
  spanning-type-span-diagram-join = A × B

  left-map-span-diagram-join :
    spanning-type-span-diagram-join → domain-span-diagram-join
  left-map-span-diagram-join = pr1

  right-map-span-diagram-join :
    spanning-type-span-diagram-join → codomain-span-diagram-join
  right-map-span-diagram-join = pr2

  span-span-diagram-join :
    span (l1 ⊔ l2) domain-span-diagram-join codomain-span-diagram-join
  pr1 span-span-diagram-join = spanning-type-span-diagram-join
  pr1 (pr2 span-span-diagram-join) = left-map-span-diagram-join
  pr2 (pr2 span-span-diagram-join) = right-map-span-diagram-join

  span-diagram-join : span-diagram l1 l2 (l1 ⊔ l2)
  pr1 span-diagram-join = domain-span-diagram-join
  pr1 (pr2 span-diagram-join) = codomain-span-diagram-join
  pr2 (pr2 span-diagram-join) = span-span-diagram-join
```

### The join of two types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  join : UU (l1 ⊔ l2)
  join = standard-pushout (span-diagram-join A B)

infixr 15 _*_
_*_ = join

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  cocone-join : cocone-span-diagram (span-diagram-join A B) (A * B)
  cocone-join = cocone-standard-pushout (span-diagram-join A B)

  universal-property-pushout-join :
    universal-property-pushout (span-diagram-join A B) (cocone-join)
  universal-property-pushout-join =
    universal-property-pushout-standard-pushout (span-diagram-join A B)

  equiv-universal-property-pushout-join :
    {l : Level} (X : UU l) → (A * B → X) ≃ cocone-span-diagram (span-diagram-join A B) X
  equiv-universal-property-pushout-join =
    equiv-universal-property-pushout-standard-pushout (span-diagram-join A B)

  inl-join : A → A * B
  inl-join = pr1 cocone-join

  inr-join : B → A * B
  inr-join = pr1 (pr2 cocone-join)

  glue-join : (t : A × B) → inl-join (pr1 t) ＝ inr-join (pr2 t)
  glue-join = pr2 (pr2 cocone-join)

  cogap-join :
    {l3 : Level} (X : UU l3) → cocone-span-diagram (span-diagram-join A B) X → A * B → X
  cogap-join X = map-inv-is-equiv (universal-property-pushout-join X)

  compute-inl-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone-span-diagram (span-diagram-join A B) X) →
    ( cogap-join X c ∘ inl-join) ~ left-map-cocone-span-diagram (span-diagram-join A B) c
  compute-inl-cogap-join =
    compute-inl-cogap-cocone-span-diagram (span-diagram-join A B)

  compute-inr-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone-span-diagram (span-diagram-join A B) X) →
    ( cogap-join X c ∘ inr-join) ~ right-map-cocone-span-diagram (span-diagram-join A B) c
  compute-inr-cogap-join =
    compute-inr-cogap-cocone-span-diagram (span-diagram-join A B)

  compute-glue-cogap-join :
    {l3 : Level} {X : UU l3} (c : cocone-span-diagram (span-diagram-join A B) X) →
    ( ( cogap-join X c ·l coherence-square-cocone-span-diagram (span-diagram-join A B) cocone-join) ∙h
      ( compute-inr-cogap-join c ·r pr2)) ~
    ( compute-inl-cogap-join c ·r pr1) ∙h coherence-square-cocone-span-diagram (span-diagram-join A B) c
  compute-glue-cogap-join =
    compute-glue-cogap-cocone-span-diagram (span-diagram-join A B)
```

## Properties

### The left unit law for joins

```agda
is-equiv-inr-join-empty :
  {l : Level} (X : UU l) → is-equiv (inr-join {A = empty} {B = X})
is-equiv-inr-join-empty X =
  is-equiv-right-map-cocone-universal-property-pushout
    ( span-diagram-join empty X)
    ( cocone-join)
    ( is-equiv-pr1-product-empty X)
    ( universal-property-pushout-join)

left-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (empty * X)
pr1 (left-unit-law-join X) = inr-join
pr2 (left-unit-law-join X) = is-equiv-inr-join-empty X

is-equiv-inr-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty A → is-equiv (inr-join {A = A} {B = B})
is-equiv-inr-join-is-empty {A = A} {B = B} is-empty-A =
  is-equiv-right-map-cocone-universal-property-pushout
    ( span-diagram-join A B)
    ( cocone-join)
    ( is-equiv-pr1-product-is-empty A B is-empty-A)
    ( universal-property-pushout-join)

left-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty A → B ≃ (A * B)
pr1 (left-unit-law-join-is-empty is-empty-A) = inr-join
pr2 (left-unit-law-join-is-empty is-empty-A) =
  is-equiv-inr-join-is-empty is-empty-A
```

### The right unit law for joins

```agda
is-equiv-inl-join-empty :
  {l : Level} (X : UU l) → is-equiv (inl-join {A = X} {B = empty})
is-equiv-inl-join-empty X =
  is-equiv-left-map-cocone-universal-property-pushout
    ( span-diagram-join X empty)
    ( cocone-join)
    ( is-equiv-pr2-product-empty X)
    ( universal-property-pushout-join)

right-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (X * empty)
pr1 (right-unit-law-join X) = inl-join
pr2 (right-unit-law-join X) = is-equiv-inl-join-empty X

is-equiv-inl-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → is-equiv (inl-join {A = A} {B = B})
is-equiv-inl-join-is-empty {A = A} {B = B} is-empty-B =
  is-equiv-left-map-cocone-universal-property-pushout
    ( span-diagram-join A B)
    ( cocone-join)
    ( is-equiv-pr2-product-is-empty A B is-empty-B)
    ( universal-property-pushout-join)

right-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → A ≃ (A * B)
pr1 (right-unit-law-join-is-empty is-empty-B) = inl-join
pr2 (right-unit-law-join-is-empty is-empty-B) =
  is-equiv-inl-join-is-empty is-empty-B

map-inv-right-unit-law-join-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-empty B → A * B → A
map-inv-right-unit-law-join-is-empty H =
  map-inv-equiv (right-unit-law-join-is-empty H)
```

### The left zero law for joins

```agda
is-equiv-inl-join-unit :
  {l : Level} (X : UU l) → is-equiv (inl-join {A = unit} {B = X})
is-equiv-inl-join-unit X =
  is-equiv-left-map-cocone-universal-property-pushout
    ( span-diagram-join unit X)
    ( cocone-join)
    ( is-equiv-map-left-unit-law-product)
    ( universal-property-pushout-join)

left-zero-law-join :
  {l : Level} (X : UU l) → is-contr (unit * X)
left-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( inl-join , is-equiv-inl-join-unit X)
    ( is-contr-unit)

is-equiv-inl-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-contr A → is-equiv (inl-join {A = A} {B = B})
is-equiv-inl-join-is-contr A B is-contr-A =
  is-equiv-left-map-cocone-universal-property-pushout
    ( span-diagram-join A B)
    ( cocone-join)
    ( is-equiv-pr2-product-is-contr is-contr-A)
    ( universal-property-pushout-join)

left-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr A → is-contr (A * B)
left-zero-law-join-is-contr A B is-contr-A =
  is-contr-equiv'
    ( A)
    ( inl-join , is-equiv-inl-join-is-contr A B is-contr-A)
    ( is-contr-A)
```

### The right zero law for joins

```agda
is-equiv-inr-join-unit :
  {l : Level} (X : UU l) → is-equiv (inr-join {A = X} {B = unit})
is-equiv-inr-join-unit X =
  is-equiv-right-map-cocone-universal-property-pushout
    ( span-diagram-join X unit)
    ( cocone-join)
    ( is-equiv-map-right-unit-law-product)
    ( universal-property-pushout-join)

right-zero-law-join :
  {l : Level} (X : UU l) → is-contr (X * unit)
right-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( inr-join , is-equiv-inr-join-unit X)
    ( is-contr-unit)

is-equiv-inr-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-contr B → is-equiv (inr-join {A = A} {B = B})
is-equiv-inr-join-is-contr A B is-contr-B =
  is-equiv-right-map-cocone-universal-property-pushout
    ( span-diagram-join A B)
    ( cocone-join)
    ( is-equiv-pr1-is-contr (λ _ → is-contr-B))
    ( universal-property-pushout-join)

right-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr B → is-contr (A * B)
right-zero-law-join-is-contr A B is-contr-B =
  is-contr-equiv'
    ( B)
    ( inr-join , is-equiv-inr-join-is-contr A B is-contr-B)
    ( is-contr-B)
```

### The join of propositions is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-proof-irrelevant-join-is-proof-irrelevant :
    is-proof-irrelevant A → is-proof-irrelevant B → is-proof-irrelevant (A * B)
  is-proof-irrelevant-join-is-proof-irrelevant
    is-proof-irrelevant-A is-proof-irrelevant-B =
    cogap-join (is-contr (A * B))
      ( pair
        ( left-zero-law-join-is-contr A B ∘ is-proof-irrelevant-A)
        ( pair
          ( right-zero-law-join-is-contr A B ∘ is-proof-irrelevant-B)
          ( λ (a , b) → center
            ( is-property-is-contr
              ( left-zero-law-join-is-contr A B (is-proof-irrelevant-A a))
              ( right-zero-law-join-is-contr A B (is-proof-irrelevant-B b))))))

  is-prop-join-is-prop :
    is-prop A → is-prop B → is-prop (A * B)
  is-prop-join-is-prop is-prop-A is-prop-B =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-join-is-proof-irrelevant
        ( is-proof-irrelevant-is-prop is-prop-A)
        ( is-proof-irrelevant-is-prop is-prop-B))

module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  join-Prop : Prop (l1 ⊔ l2)
  pr1 join-Prop = (type-Prop P) * (type-Prop Q)
  pr2 join-Prop =
    is-prop-join-is-prop (is-prop-type-Prop P) (is-prop-type-Prop Q)

  type-join-Prop : UU (l1 ⊔ l2)
  type-join-Prop = type-Prop join-Prop

  is-prop-type-join-Prop : is-prop type-join-Prop
  is-prop-type-join-Prop = is-prop-type-Prop join-Prop

  inl-join-Prop : type-hom-Prop P join-Prop
  inl-join-Prop = inl-join

  inr-join-Prop : type-hom-Prop Q join-Prop
  inr-join-Prop = inr-join
```

## See also

- [Joins of maps](synthetic-homotopy-theory.joins-of-maps.md)
- [Pushout-products](synthetic-homotopy-theory.pushout-products.md)
- [Dependent pushout-products](synthetic-homotopy-theory.dependent-pushout-products.md)
- [Disjunction](foundation.disjunction.md) is the join of two propositions

## References

- Egbert Rijke, _The join construction_, 2017
  ([arXiv:1701.07538](https://arxiv.org/abs/1701.07538))
