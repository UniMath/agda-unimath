# Uniqueness quantification

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.uniqueness-quantification
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Given a predicate `P : A → Prop` we say there
{{#concept "uniquely exists" Disambiguation="in a subtype" WDID=Q2502253 WD="uniqueness quantification" Agda=∃!}}
_an `x : A` satisfying `P`_, if the [subtype](foundation-core.subtypes.md)
`Σ (x : A), (P x)` is [contractible](foundation-core.contractible-types.md).

More generally, given a [structure](foundation.structure.md) `B : A → 𝒰` we say
there
{{#concept "uniquely exists" Disambiguation="structure" Agda=uniquely-exists-structure}}
_an `x : A` and a `y : B x`_, if the
[total type](foundation.dependent-pair-types.md) `Σ (x : A), (B x)` is
contractible.

Note that the unique existence of structure is defined in the exact same way as
the concept of
[torsorial type families](foundation-core.torsorial-type-families.md). Whether
to use the concept of unique existence of a structure or the concept of
torsorial type family is dependent on the context. Torsoriality is used often to
emphasize the relation of the type family to the identity type, whereas
uniqueness of structure is used to emphasize the uniqueness of elements equipped
with further structure. For example, we tend to use unique existence in
combination with universal properties, in order to conclude that a certain map
equipped with some homotopies exists uniquely.

As a special case of uniqueness quantification, we recover
[exclusive disjunction](foundation.exclusive-disjunction.md) when the indexing
type is a [2-element type](univalent-combinatorics.2-element-types.md).
Concretely, we have the equivalence

```text
  ∃! (t : bool), (P t) ≐ is-contr (Σ (t : bool), (P t))
                       ≃ is-contr ((P false) + (P true))
                       ≐ P false ⊻ P true.
```

## Definitions

### Unique existence of structure

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  uniquely-exists-structure-Prop : Prop (l1 ⊔ l2)
  uniquely-exists-structure-Prop = is-torsorial-Prop B

  uniquely-exists-structure : UU (l1 ⊔ l2)
  uniquely-exists-structure = type-Prop uniquely-exists-structure-Prop

  is-prop-uniquely-exists-structure : is-prop uniquely-exists-structure
  is-prop-uniquely-exists-structure =
    is-prop-type-Prop uniquely-exists-structure-Prop
```

### Unique existence in a subtype

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  uniquely-exists-Prop : Prop (l1 ⊔ l2)
  uniquely-exists-Prop = uniquely-exists-structure-Prop A (type-Prop ∘ P)

  uniquely-exists : UU (l1 ⊔ l2)
  uniquely-exists = type-Prop uniquely-exists-Prop

  is-prop-uniquely-exists : is-prop uniquely-exists
  is-prop-uniquely-exists = is-prop-type-Prop uniquely-exists-Prop

  ∃! : Prop (l1 ⊔ l2)
  ∃! = uniquely-exists-Prop
```

### Components of unique existence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  pair-uniquely-exists : uniquely-exists-structure A B → Σ A B
  pair-uniquely-exists = center

  pr1-uniquely-exists : uniquely-exists-structure A B → A
  pr1-uniquely-exists = pr1 ∘ pair-uniquely-exists

  pr2-uniquely-exists :
    (p : uniquely-exists-structure A B) → B (pr1-uniquely-exists p)
  pr2-uniquely-exists = pr2 ∘ pair-uniquely-exists

  contraction-uniquely-exists :
    (p : uniquely-exists-structure A B) →
    (q : Σ A B) → pair-uniquely-exists p ＝ q
  contraction-uniquely-exists = contraction
```

## See also

- Unique existence is the indexed counterpart to
  [exclusive disjunction](foundation.exclusive-disjunction.md).
- A different name for _unique existence_ is
  [torsoriality](foundation.torsorial-type-families.md).

## External links

- [uniqueness quantifier](https://ncatlab.org/nlab/show/uniqueness+quantifier)
  at $n$Lab
- [Uniqueness quantification](https://en.wikipedia.org/wiki/Uniqueness_quantification)
  at Wikipedia
