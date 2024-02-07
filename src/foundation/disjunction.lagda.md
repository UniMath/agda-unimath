# Disjunction of propositions

```agda
module foundation.disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.span-diagrams
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import synthetic-homotopy-theory.action-functions-cocones-under-span-diagrams
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The
{{#concept "disjunction" Disambiguation="propositions" Agda=disjunction-Prop}}
`P ∨ Q` of two [propositions](foundation-core.propositions.md) `P` and `Q` is
the proposition that `P` holds or `Q` holds.

The {{#concept "introduction rules" Disambiguation="disjunction of propositions"}} of `P ∨ Q` are two implications

```text
  P ⇒ P ∨ Q
  Q ⇒ P ∨ Q.
```

In other words, the basic way of showing that the proposition `P ∨ Q` holds is by showing that either `P` holds or that `Q` holds.

The {{#concept elimination rule" Disambiguation="disjunction of propositions"}} of `P ∨ Q` is that for any proposition `R` there is an implication

```text
  (P ⇒ R) ∧ (Q ⇒ R) ⇒ (P ∨ Q ⇒ R).
```

In other words, to show that `P ∨ Q` implies a proposition `R`, we have to show that both `P` implies `R` and `Q` implies `R`. Indeed, if we have an unknown proof `p` of the proposition `P ∨ Q` and we want to use it to conclude `R`, then `p` either comes from the proposition `P` or from the proposition `Q`. It therefore suffices to show that both `P ⇒ R` and `Q ⇒ R`.

The disjunction of two propositions can be defined in several ways. The standard definition of the proposition `P ∨ Q` is as the [propositional truncation](foundation.propositional-truncations.md) of the [coproduct](foundation.coproduct-types.md) of `P` and `Q`, i.e.,

```text
  P ∨ Q := ∥ P + Q ∥.
```

However, one can also show that the [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
            pr2
    P × Q -----> Q
      |          |
  pr1 |          |
      ∨          ∨
      P -----> P ∨ Q
```

is a [pushout square](synthetic-homotopy-theory.pushouts.md). In other words, the disjunction `P ∨ Q` is the [join](synthetic-homotopy-theory.joins-of-types.md) of `P` and `Q`. Thus we could alternatively have defined

```text
  P ∨ Q := P * Q.
```

## Definitions

### The disjunction of two propositions

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where
  
  disjunction-Prop : Prop (l1 ⊔ l2)
  disjunction-Prop = trunc-Prop (type-Prop P + type-Prop Q)

  type-disjunction-Prop : UU (l1 ⊔ l2)
  type-disjunction-Prop = type-Prop disjunction-Prop

  abstract
    is-prop-type-disjunction-Prop : is-prop type-disjunction-Prop
    is-prop-type-disjunction-Prop = is-prop-type-Prop disjunction-Prop

infixr 10 _∨_
_∨_ = type-disjunction-Prop
```

**Note**: The symbol used for the disjunction `_∨_` is the
[logical or](https://codepoints.net/U+2228) `∨` (agda-input: `\vee` `\or`), and
not the [latin small letter v](https://codepoints.net/U+0076) `v`.

### The introduction rules for disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where
  
  inl-disjunction-Prop : type-hom-Prop P (disjunction-Prop P Q)
  inl-disjunction-Prop = unit-trunc-Prop ∘ inl

  inr-disjunction-Prop : type-hom-Prop Q (disjunction-Prop P Q)
  inr-disjunction-Prop = unit-trunc-Prop ∘ inr
```

### The cocone structure on the disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  span-diagram-disjunction-Prop : span-diagram l1 l2 (l1 ⊔ l2)
  span-diagram-disjunction-Prop = span-diagram-join (type-Prop P) (type-Prop Q)

  coherence-square-cocone-disjunction-Prop :
    coherence-square-maps
      ( pr2)
      ( pr1)
      ( inr-disjunction-Prop P Q)
      ( inl-disjunction-Prop P Q)
  coherence-square-cocone-disjunction-Prop x =
    eq-is-prop (is-prop-type-disjunction-Prop P Q)

  cocone-disjunction-Prop :
    cocone-span-diagram
      ( span-diagram-disjunction-Prop)
      ( type-disjunction-Prop P Q)
  pr1 cocone-disjunction-Prop = inl-disjunction-Prop P Q
  pr1 (pr2 cocone-disjunction-Prop) = inr-disjunction-Prop P Q
  pr2 (pr2 cocone-disjunction-Prop) = coherence-square-cocone-disjunction-Prop
```

## Properties

### The elimination rule and universal property of disjunction

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) (Q : Prop l2) (R : Prop l3)
  where
  
  ev-disjunction-Prop :
    type-hom-Prop
      ( hom-Prop (disjunction-Prop P Q) R)
      ( conjunction-Prop (hom-Prop P R) (hom-Prop Q R))
  pr1 (ev-disjunction-Prop h) = h ∘ (inl-disjunction-Prop P Q)
  pr2 (ev-disjunction-Prop h) = h ∘ (inr-disjunction-Prop P Q)

  elim-disjunction-Prop :
    type-hom-Prop
      ( conjunction-Prop (hom-Prop P R) (hom-Prop Q R))
      ( hom-Prop (disjunction-Prop P Q) R)
  elim-disjunction-Prop (pair f g) =
    map-universal-property-trunc-Prop R (rec-coproduct f g)

  abstract
    is-equiv-ev-disjunction-Prop : is-equiv ev-disjunction-Prop
    is-equiv-ev-disjunction-Prop =
      is-equiv-is-prop
        ( is-prop-type-Prop (hom-Prop (disjunction-Prop P Q) R))
        ( is-prop-type-Prop (conjunction-Prop (hom-Prop P R) (hom-Prop Q R)))
        ( elim-disjunction-Prop)
```

### The unit laws for disjunction

```agda
module _
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  where

  map-left-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop P) → type-disjunction-Prop P Q → type-Prop Q
  map-left-unit-law-disjunction-is-empty-Prop f =
    elim-disjunction-Prop P Q Q (ex-falso ∘ f , id)

  map-right-unit-law-disjunction-is-empty-Prop :
    is-empty (type-Prop Q) → type-disjunction-Prop P Q → type-Prop P
  map-right-unit-law-disjunction-is-empty-Prop f =
    elim-disjunction-Prop P Q P (id , ex-falso ∘ f)
```

### Disjunction is the join of propositions

```agda
module _
  {l1 l2 : Level} (A : Prop l1) (B : Prop l2)
  where

  map-disjunction-join-Prop : type-join-Prop A B → type-disjunction-Prop A B
  map-disjunction-join-Prop =
    cogap-join (type-disjunction-Prop A B) (cocone-disjunction-Prop A B)

  map-join-disjunction-Prop : type-disjunction-Prop A B → type-join-Prop A B
  map-join-disjunction-Prop =
    elim-disjunction-Prop A B
      ( join-Prop A B)
      ( inl-join-Prop A B , inr-join-Prop A B)

  is-equiv-map-disjunction-join-Prop : is-equiv map-disjunction-join-Prop
  is-equiv-map-disjunction-join-Prop =
    is-equiv-is-prop
      ( is-prop-type-join-Prop A B)
      ( is-prop-type-disjunction-Prop A B)
      ( map-join-disjunction-Prop)

  equiv-disjunction-join-Prop :
    (type-join-Prop A B) ≃ (type-disjunction-Prop A B)
  pr1 equiv-disjunction-join-Prop = map-disjunction-join-Prop
  pr2 equiv-disjunction-join-Prop = is-equiv-map-disjunction-join-Prop

  is-equiv-map-join-disjunction-Prop : is-equiv map-join-disjunction-Prop
  is-equiv-map-join-disjunction-Prop =
    is-equiv-is-prop
      ( is-prop-type-disjunction-Prop A B)
      ( is-prop-type-join-Prop A B)
      ( map-disjunction-join-Prop)

  equiv-join-disjunction-Prop :
    (type-disjunction-Prop A B) ≃ (type-join-Prop A B)
  pr1 equiv-join-disjunction-Prop = map-join-disjunction-Prop
  pr2 equiv-join-disjunction-Prop = is-equiv-map-join-disjunction-Prop

  htpy-cocone-span-diagram-disjunction-Prop :
    htpy-cocone-span-diagram
      ( span-diagram-disjunction-Prop A B)
      ( cocone-map-span-diagram
        ( span-diagram-disjunction-Prop A B)
        ( cocone-join)
        ( map-disjunction-join-Prop))
      ( cocone-disjunction-Prop A B)
  pr1 htpy-cocone-span-diagram-disjunction-Prop _ =
    eq-is-prop (is-prop-type-disjunction-Prop A B)
  pr1 (pr2 htpy-cocone-span-diagram-disjunction-Prop) _ =
    eq-is-prop (is-prop-type-disjunction-Prop A B)
  pr2 (pr2 htpy-cocone-span-diagram-disjunction-Prop) _ =
    eq-is-prop (is-prop-is-contr (is-prop-type-disjunction-Prop A B _ _))

  universal-property-pushout-join-disjunction :
    universal-property-pushout
      ( span-diagram-disjunction-Prop A B)
      ( cocone-disjunction-Prop A B)
  universal-property-pushout-join-disjunction =
    universal-property-pushout-universal-property-pushout-is-equiv
      ( span-diagram-disjunction-Prop A B)
      ( cocone-join)
      ( cocone-disjunction-Prop A B)
      ( map-disjunction-join-Prop)
      ( htpy-cocone-span-diagram-disjunction-Prop)
      ( is-equiv-map-disjunction-join-Prop)
      ( universal-property-pushout-join)
```

## See also

- [Disjunction on decidable propositions](foundation.disjunction-decidable-propositions.md)
