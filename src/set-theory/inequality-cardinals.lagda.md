# Inequality on cardinals

```agda
module set-theory.inequality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.mere-decidable-embeddings
open import foundation.mere-embeddings
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders

open import set-theory.cardinals
open import set-theory.complemented-inequality-cardinals
open import set-theory.decidable-cardinals
open import set-theory.equality-cardinals
open import set-theory.indexed-inequality-cardinals
open import set-theory.inhabited-cardinals
open import set-theory.projective-cardinals
```

</details>

## Idea

We say a [cardinal](set-theory.cardinals.md) `X` is
{{#concept "less than or equal to" Disambiguation="cardinals" Agda=leq-Cardinal}}
a cardinal `Y` if any [set](foundation-core.sets.md) in the isomorphism class of
`X` embeds into any set in the isomorphism class of `Y`. This defines the
{{#concept "standard ordering" Disambiguation="on cardinalities of sets" Agda=large-preorder-Cardinal}}
on cardinals.

Under the assumption of the
[law of excluded middle](foundation.law-of-excluded-middle.md) this relation is
antisymmetric and hence defines a [partial order](order-theory.posets.md), due
to
[the Cantor–Schröder–Bernstein theorem](foundation.cantor-schroder-bernstein-escardo.md).

## Definition

### Boundedness of the cardinality of a set

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  leq-prop-Cardinal' : Cardinal l2 → Prop (l1 ⊔ l2)
  leq-prop-Cardinal' =
    map-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → mere-emb-Prop (type-Set X) (type-Set Y'))

  compute-leq-prop-Cardinal' :
    (Y : Set l2) →
    leq-prop-Cardinal' (cardinality Y) ＝
    mere-emb-Prop (type-Set X) (type-Set Y)
  compute-leq-prop-Cardinal' =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → mere-emb-Prop (type-Set X) (type-Set Y'))
```

### Inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  leq-prop-Cardinal : Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  leq-prop-Cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( leq-prop-Cardinal')

  leq-Cardinal : Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  leq-Cardinal X Y = type-Prop (leq-prop-Cardinal X Y)

  is-prop-leq-Cardinal :
    {X : Cardinal l1} {Y : Cardinal l2} → is-prop (leq-Cardinal X Y)
  is-prop-leq-Cardinal {X} {Y} = is-prop-type-Prop (leq-prop-Cardinal X Y)
```

### Inequality of cardinalities

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  leq-prop-cardinality : Prop (l1 ⊔ l2)
  leq-prop-cardinality = leq-prop-Cardinal (cardinality X) (cardinality Y)

  leq-cardinality : UU (l1 ⊔ l2)
  leq-cardinality = leq-Cardinal (cardinality X) (cardinality Y)

  is-prop-leq-cardinality : is-prop leq-cardinality
  is-prop-leq-cardinality = is-prop-leq-Cardinal

  eq-compute-leq-prop-cardinality :
    leq-prop-cardinality ＝ mere-emb-Prop (type-Set X) (type-Set Y)
  eq-compute-leq-prop-cardinality =
    ( htpy-eq
      ( triangle-universal-property-trunc-Set
        ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
        ( leq-prop-Cardinal') X) (cardinality Y)) ∙
    ( compute-leq-prop-Cardinal' X Y)

  eq-compute-leq-cardinality :
    leq-cardinality ＝ mere-emb (type-Set X) (type-Set Y)
  eq-compute-leq-cardinality =
    ap type-Prop eq-compute-leq-prop-cardinality

  compute-leq-cardinality :
    leq-cardinality ≃ mere-emb (type-Set X) (type-Set Y)
  compute-leq-cardinality = equiv-eq eq-compute-leq-cardinality

  unit-leq-cardinality :
    mere-emb (type-Set X) (type-Set Y) → leq-cardinality
  unit-leq-cardinality = map-inv-equiv compute-leq-cardinality

  inv-unit-leq-cardinality :
    leq-cardinality → mere-emb (type-Set X) (type-Set Y)
  inv-unit-leq-cardinality = pr1 compute-leq-cardinality
```

### Inequality on cardinals is reflexive

```agda
refl-leq-cardinality : is-reflexive-Large-Relation Set leq-cardinality
refl-leq-cardinality A = unit-leq-cardinality A A (refl-mere-emb (type-Set A))

refl-leq-Cardinal : is-reflexive-Large-Relation Cardinal leq-Cardinal
refl-leq-Cardinal =
  apply-dependent-universal-property-trunc-Set'
    ( λ X → set-Prop (leq-prop-Cardinal X X))
    ( refl-leq-cardinality)
```

### Inequality on cardinals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  where

  transitive-leq-cardinality :
    (X : Set l1) (Y : Set l2) (Z : Set l3) →
    leq-cardinality Y Z → leq-cardinality X Y → leq-cardinality X Z
  transitive-leq-cardinality X Y Z Y≤Z X≤Y =
    unit-leq-cardinality X Z
      ( transitive-mere-emb
        ( inv-unit-leq-cardinality Y Z Y≤Z)
        ( inv-unit-leq-cardinality X Y X≤Y))

  transitive-leq-Cardinal :
    (X : Cardinal l1) (Y : Cardinal l2) (Z : Cardinal l3) →
    leq-Cardinal Y Z → leq-Cardinal X Y → leq-Cardinal X Z
  transitive-leq-Cardinal =
    apply-thrice-dependent-universal-property-trunc-Set'
      ( λ X Y Z →
        ( leq-Cardinal Y Z → leq-Cardinal X Y → leq-Cardinal X Z) ,
        ( is-set-function-type
          ( is-set-function-type
            ( is-set-is-prop is-prop-leq-Cardinal))))
      ( transitive-leq-cardinality)
```

## Properties

### Assuming excluded middle, then inequality is antisymmetric

Using that mere equivalence characterizes equality of cardinals we can conclude
by the Cantor–Schröder–Bernstein theorem, assuming the law of excluded middle,
that `leq-Cardinal` is antisymmetric and hence a partial order.

```agda
module _
  {l : Level} (lem : level-LEM l)
  where

  antisymmetric-leq-cardinality :
    (X Y : Set l) →
    leq-cardinality X Y →
    leq-cardinality Y X →
    cardinality X ＝ cardinality Y
  antisymmetric-leq-cardinality X Y X≤Y Y≤X =
    eq-mere-equiv-cardinality X Y
      ( antisymmetric-mere-emb
        ( lem)
        ( inv-unit-leq-cardinality X Y X≤Y)
        ( inv-unit-leq-cardinality Y X Y≤X))

  antisymmetric-leq-Cardinal :
    (X Y : Cardinal l) →
    leq-Cardinal X Y → leq-Cardinal Y X → X ＝ Y
  antisymmetric-leq-Cardinal =
    apply-twice-dependent-universal-property-trunc-Set'
      ( λ X Y →
        set-Prop
          ( function-Prop
            ( leq-Cardinal X Y)
            ( function-Prop (leq-Cardinal Y X) (Id-Prop (Cardinal-Set l) X Y))))
      ( antisymmetric-leq-cardinality)
```

### The large poset of cardinals

```agda
large-preorder-Cardinal : Large-Preorder lsuc (_⊔_)
large-preorder-Cardinal =
  λ where
  .type-Large-Preorder → Cardinal
  .leq-prop-Large-Preorder → leq-prop-Cardinal
  .refl-leq-Large-Preorder → refl-leq-Cardinal
  .transitive-leq-Large-Preorder → transitive-leq-Cardinal

large-poset-Cardinal : LEM → Large-Poset lsuc (_⊔_)
large-poset-Cardinal lem =
  λ where
  .large-preorder-Large-Poset → large-preorder-Cardinal
  .antisymmetric-leq-Large-Poset → antisymmetric-leq-Cardinal lem
```

### Complemented inequality implies inequality

```agda
leq-leq-complemented-Cardinal :
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2) →
  leq-complemented-Cardinal X Y → leq-Cardinal X Y
leq-leq-complemented-Cardinal =
  apply-twice-dependent-universal-property-trunc-Set'
    ( λ X Y →
      set-Prop
        ( function-Prop
          ( leq-complemented-Cardinal X Y)
          ( leq-prop-Cardinal X Y)))
    ( λ X Y →
      unit-leq-cardinality X Y ∘
      mere-emb-mere-decidable-emb ∘
      inv-unit-leq-complemented-cardinality X Y)
```

### Given a decidable cardinal `X` such that there is some cardinal `Y` with `X ≰ Y`, then `X` is inhabited

```agda
is-inhabited-is-not-leq-Cardinal :
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2) →
  is-decidable-Cardinal X →
  ¬ leq-Cardinal X Y → is-inhabited-Cardinal X
is-inhabited-is-not-leq-Cardinal X Y dX H =
  is-inhabited-is-not-leq-complemented-Cardinal X Y dX
    ( H ∘ leq-leq-complemented-Cardinal X Y)
```

### If `X` is projective and `X ≤ⁱ Y` then `X ≤ Y`

```agda
leq-is-projective-leq-indexed-Cardinal :
  {l1 l2 : Level} (X : Cardinal l1) (Y : Cardinal l2) →
  is-projective-Cardinal (l1 ⊔ l2) X →
  leq-indexed-Cardinal X Y → leq-Cardinal X Y
leq-is-projective-leq-indexed-Cardinal {l1} {l2} =
  apply-twice-dependent-universal-property-trunc-Set'
    ( λ X Y →
      set-Prop
        ( function-Prop (is-projective-Cardinal (l1 ⊔ l2) X)
          ( function-Prop (leq-indexed-Cardinal X Y)
            ( leq-prop-Cardinal X Y))))
    ( λ X Y pX H →
      rec-trunc-Prop
        ( leq-prop-cardinality X Y)
        ( λ f →
          unit-leq-cardinality X Y
            ( reverse-mere-emb-surjection-is-projective
              ( inv-unit-is-projective-cardinality X pX)
              ( is-set-type-Set Y) f))
        ( inv-unit-leq-indexed-cardinality X Y H))
```

## See also

- [Complemented inequality of cardinals](set-theory.complemented-inequality-cardinals.md)
