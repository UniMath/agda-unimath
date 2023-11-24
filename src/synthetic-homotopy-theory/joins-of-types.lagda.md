# Joins of types

```agda
module synthetic-homotopy-theory.joins-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **join** of `A` and `B` is the
[pushout](synthetic-homotopy-theory.pushouts.md) of the
[span](foundation.spans.md) `A ← A × B → B`.

## Definition

```agda
join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
join A B = pushout (pr1 {A = A} {B = λ _ → B}) pr2

infixr 15 _*_
_*_ = join

cocone-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  cocone (pr1 {A = A} {B = λ _ → B}) pr2 (A * B)
cocone-join A B = cocone-pushout pr1 pr2

up-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  {l : Level} → universal-property-pushout l pr1 pr2 (cocone-join A B)
up-join A B = up-pushout pr1 pr2

equiv-up-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  {l : Level} (X : UU l) → (A * B → X) ≃ cocone pr1 pr2 X
equiv-up-join A B = equiv-up-pushout pr1 pr2

inl-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → A → A * B
inl-join A B = pr1 (cocone-join A B)

inr-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → B → A * B
inr-join A B = pr1 (pr2 (cocone-join A B))

glue-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (t : A × B) →
  Id (inl-join A B (pr1 t)) (inr-join A B (pr2 t))
glue-join A B = pr2 (pr2 (cocone-join A B))

cogap-join :
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (X : UU l3) →
  cocone pr1 pr2 X → A * B → X
cogap-join A B X = map-inv-is-equiv (up-join A B X)
```

## Properties

### The left unit law for joins

```agda
is-equiv-inr-join-empty :
  {l : Level} (X : UU l) → is-equiv (inr-join empty X)
is-equiv-inr-join-empty X =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join empty X)
    ( is-equiv-pr1-prod-empty X)
    ( up-join empty X)

left-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (empty * X)
pr1 (left-unit-law-join X) = inr-join empty X
pr2 (left-unit-law-join X) = is-equiv-inr-join-empty X

is-equiv-inr-join-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-empty A → is-equiv (inr-join A B)
is-equiv-inr-join-is-empty A B is-empty-A =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join A B)
    ( is-equiv-pr1-prod-is-empty A B is-empty-A)
    ( up-join A B)

left-unit-law-join-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-empty A → B ≃ (A * B)
pr1 (left-unit-law-join-is-empty A B is-empty-A) = inr-join A B
pr2 (left-unit-law-join-is-empty A B is-empty-A) =
  is-equiv-inr-join-is-empty A B is-empty-A
```

### The right unit law for joins

```agda
is-equiv-inl-join-empty :
  {l : Level} (X : UU l) → is-equiv (inl-join X empty)
is-equiv-inl-join-empty X =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join X empty)
    ( is-equiv-pr2-prod-empty X)
    ( up-join X empty)

right-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (X * empty)
pr1 (right-unit-law-join X) = inl-join X empty
pr2 (right-unit-law-join X) = is-equiv-inl-join-empty X

is-equiv-inl-join-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-empty B → is-equiv (inl-join A B)
is-equiv-inl-join-is-empty A B is-empty-B =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join A B)
    ( is-equiv-pr2-prod-is-empty A B is-empty-B)
    ( up-join A B)

right-unit-law-join-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-empty B → A ≃ (A * B)
pr1 (right-unit-law-join-is-empty A B is-empty-B) = inl-join A B
pr2 (right-unit-law-join-is-empty A B is-empty-B) =
  is-equiv-inl-join-is-empty A B is-empty-B
```

### The left zero law for joins

```agda
is-equiv-inl-join-unit :
  {l : Level} (X : UU l) → is-equiv (inl-join unit X)
is-equiv-inl-join-unit X =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join unit X)
    ( is-equiv-map-left-unit-law-prod)
    ( up-join unit X)

left-zero-law-join :
  {l : Level} (X : UU l) → is-contr (unit * X)
left-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( pair (inl-join unit X) (is-equiv-inl-join-unit X))
    ( is-contr-unit)

is-equiv-inl-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr A → is-equiv (inl-join A B)
is-equiv-inl-join-is-contr A B is-contr-A =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join A B)
    ( is-equiv-pr2-prod-is-contr is-contr-A)
    ( up-join A B)

left-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr A → is-contr (A * B)
left-zero-law-join-is-contr A B is-contr-A =
  is-contr-equiv'
    ( A)
    ( pair (inl-join A B) (is-equiv-inl-join-is-contr A B is-contr-A))
    ( is-contr-A)
```

### The right zero law for joins

```agda
is-equiv-inr-join-unit :
  {l : Level} (X : UU l) → is-equiv (inr-join X unit)
is-equiv-inr-join-unit X =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join X unit)
    ( is-equiv-map-right-unit-law-prod)
    ( up-join X unit)

right-zero-law-join :
  {l : Level} (X : UU l) → is-contr (X * unit)
right-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( pair (inr-join X unit) (is-equiv-inr-join-unit X))
    ( is-contr-unit)

is-equiv-inr-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr B → is-equiv (inr-join A B)
is-equiv-inr-join-is-contr A B is-contr-B =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join A B)
    ( is-equiv-pr1-is-contr λ a → is-contr-B)
    ( up-join A B)

right-zero-law-join-is-contr :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-contr B → is-contr (A * B)
right-zero-law-join-is-contr A B is-contr-B =
  is-contr-equiv'
    ( B)
    ( pair (inr-join A B) (is-equiv-inr-join-is-contr A B is-contr-B))
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
    cogap-join A B (is-contr (A * B))
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
  {l1 l2 : Level} ((A , is-prop-A) : Prop l1) ((B , is-prop-B) : Prop l2)
  where

  join-Prop : Prop (l1 ⊔ l2)
  pr1 join-Prop = A * B
  pr2 join-Prop = is-prop-join-is-prop is-prop-A is-prop-B

  type-join-Prop : UU (l1 ⊔ l2)
  type-join-Prop = type-Prop join-Prop

  is-prop-type-join-Prop : is-prop type-join-Prop
  is-prop-type-join-Prop = is-prop-type-Prop join-Prop

  inl-join-Prop : type-hom-Prop (A , is-prop-A) join-Prop
  inl-join-Prop = inl-join A B

  inr-join-Prop : type-hom-Prop (B , is-prop-B) join-Prop
  inr-join-Prop = inr-join A B
```

### Disjunction is the join of propositions

```agda
module _
  {l1 l2 : Level} (A : Prop l1) (B : Prop l2)
  where

  cocone-disj : cocone pr1 pr2 (type-disj-Prop A B)
  pr1 cocone-disj = inl-disj-Prop A B
  pr1 (pr2 cocone-disj) = inr-disj-Prop A B
  pr2 (pr2 cocone-disj) (a , b) =
    eq-is-prop'
      ( is-prop-type-disj-Prop A B)
      ( inl-disj-Prop A B a)
      ( inr-disj-Prop A B b)

  map-disj-join-Prop : type-join-Prop A B → type-disj-Prop A B
  map-disj-join-Prop =
    cogap-join (type-Prop A) (type-Prop B) (type-disj-Prop A B) cocone-disj

  map-join-disj-Prop : type-disj-Prop A B → type-join-Prop A B
  map-join-disj-Prop =
    elim-disj-Prop A B
      ( join-Prop A B)
      ( pair (inl-join-Prop A B) (inr-join-Prop A B))

  is-equiv-map-disj-join-Prop : is-equiv map-disj-join-Prop
  is-equiv-map-disj-join-Prop =
    is-equiv-is-prop
      ( is-prop-type-join-Prop A B)
      ( is-prop-type-disj-Prop A B)
      ( map-join-disj-Prop)

  equiv-disj-join-Prop : (type-join-Prop A B) ≃ (type-disj-Prop A B)
  pr1 equiv-disj-join-Prop = map-disj-join-Prop
  pr2 equiv-disj-join-Prop = is-equiv-map-disj-join-Prop

  is-equiv-map-join-disj-Prop : is-equiv map-join-disj-Prop
  is-equiv-map-join-disj-Prop =
    is-equiv-is-prop
      ( is-prop-type-disj-Prop A B)
      ( is-prop-type-join-Prop A B)
      ( map-disj-join-Prop)

  equiv-join-disj-Prop : (type-disj-Prop A B) ≃ (type-join-Prop A B)
  pr1 equiv-join-disj-Prop = map-join-disj-Prop
  pr2 equiv-join-disj-Prop = is-equiv-map-join-disj-Prop

  up-join-disj : {l : Level} → universal-property-pushout l pr1 pr2 cocone-disj
  up-join-disj =
    up-pushout-up-pushout-is-equiv
      ( pr1)
      ( pr2)
      ( cocone-join (pr1 A) (pr1 B))
      ( cocone-disj)
      ( map-disj-join-Prop)
      ( pair
        ( λ _ → eq-is-prop (is-prop-type-disj-Prop A B))
        ( pair
          ( λ _ → eq-is-prop (is-prop-type-disj-Prop A B))
          ( λ (a , b) →
            eq-is-contr
              ( is-prop-type-disj-Prop A B
                ( horizontal-map-cocone pr1 pr2
                  ( cocone-map pr1 pr2
                    ( cocone-join (pr1 A) (pr1 B))
                    ( map-disj-join-Prop))
                  ( a))
                ( vertical-map-cocone pr1 pr2 cocone-disj b)))))
      ( is-equiv-map-disj-join-Prop)
      ( up-join (pr1 A) (pr1 B))
```

## See also

- [Joins of maps](synthetic-homotopy-theory.joins-of-maps.md)
- [Pushout-products](synthetic-homotopy-theory.pushout-products.md)
- [Dependent pushout-products](synthetic-homotopy-theory.dependent-pushout-products.md)

## References

- Egbert Rijke, _The join construction_, 2017
  ([arXiv:1701.07538](https://arxiv.org/abs/1701.07538))
