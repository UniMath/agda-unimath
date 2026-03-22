# Dependent products of binary relations

```agda
module foundation.dependent-products-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "dependent product" Disambiguation="of a family of binary relations" Agda=Π-Relation}}
of a family of [binary relations](foundation.binary-relations.md) `Rᵢ` on types
`Aᵢ` indexed by `i : I` is a binary relation on the type `(i : I) → A i`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  {A : I → UU l2}
  where

  Π-Relation :
    ((i : I) → Relation l3 (A i)) → Relation (l1 ⊔ l3) ((i : I) → A i)
  Π-Relation R f g = (i : I) → R i (f i) (g i)

  Π-Relation-Prop :
    ((i : I) → Relation-Prop l3 (A i)) → Relation-Prop (l1 ⊔ l3) ((i : I) → A i)
  Π-Relation-Prop R f g =
    Π-Prop I (λ i → R i (f i) (g i))
```

## Properties

### Dependent products preserve reflexivity

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  {A : I → UU l2}
  (R : (i : I) → Relation l3 (A i))
  where

  abstract
    is-reflexive-Π-Relation :
      ((i : I) → is-reflexive (R i)) → is-reflexive (Π-Relation I R)
    is-reflexive-Π-Relation refl-R i x = refl-R x (i x)
```

### Dependent products preserve symmetry

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  {A : I → UU l2}
  (R : (i : I) → Relation l3 (A i))
  where

  abstract
    is-symmetric-Π-Relation :
      ((i : I) → is-symmetric (R i)) → is-symmetric (Π-Relation I R)
    is-symmetric-Π-Relation sym-R f g Rfg i = sym-R i (f i) (g i) (Rfg i)
```

### Dependent products preserve transitivity

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  {A : I → UU l2}
  (R : (i : I) → Relation l3 (A i))
  where

  abstract
    is-transitive-Π-Relation :
      ((i : I) → is-transitive (R i)) → is-transitive (Π-Relation I R)
    is-transitive-Π-Relation trans-R f g h Rgh Rfg i =
      trans-R i (f i) (g i) (h i) (Rgh i) (Rfg i)
```

### Dependent products preserve antisymmetry

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  {A : I → UU l2}
  (R : (i : I) → Relation l3 (A i))
  where

  abstract
    htpy-is-antisymmetric-Π-Relation :
      ((i : I) → is-antisymmetric (R i)) →
      (f g : (i : I) → A i) → Π-Relation I R f g → Π-Relation I R g f → f ~ g
    htpy-is-antisymmetric-Π-Relation antisym-R f g Rfg Rgf i =
      antisym-R i (f i) (g i) (Rfg i) (Rgf i)

    is-antisymmetric-Π-Relation :
      ((i : I) → is-antisymmetric (R i)) → is-antisymmetric (Π-Relation I R)
    is-antisymmetric-Π-Relation antisym-R f g Rfg Rgf =
      eq-htpy (htpy-is-antisymmetric-Π-Relation antisym-R f g Rfg Rgf)
```
