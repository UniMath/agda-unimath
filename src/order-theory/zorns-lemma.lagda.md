# Zorn's lemma

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.zorns-lemma
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext univalence truncations
open import foundation.existential-quantification funext univalence truncations
open import foundation.inhabited-types funext univalence truncations
open import foundation.law-of-excluded-middle funext univalence truncations
open import foundation.logical-equivalences funext
open import foundation.propositional-truncations funext univalence
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.propositions

open import order-theory.chains-posets funext univalence truncations
open import order-theory.posets funext univalence truncations
open import order-theory.top-elements-posets funext univalence truncations
open import order-theory.upper-bounds-chains-posets funext univalence truncations
```

</details>

## Idea

{{#concept "Zorn's lemma" Disambiguation="for posets" WD="Zorn's lemma" WDID=Q290810 Agda=zorns-lemma}}
states that a [poset](order-theory.posets.md) where every
[chain](order-theory.chains-posets.md) has an
[upper bound](order-theory.upper-bounds-chains-posets.md) has a
[top element](order-theory.top-elements-posets.md).

## Statement

### Zorn's lemma

```agda
module _
  (l1 l2 l3 : Level)
  where

  zorns-lemma-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  zorns-lemma-Prop =
    Π-Prop
      ( Poset l1 l2)
      ( λ X →
          function-Prop
            ( (C : chain-Poset l3 X) → has-upper-bound-chain-Poset X C)
            ( ∃ (type-Poset X) (is-top-element-prop-Poset X)))

  zorns-lemma : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  zorns-lemma = type-Prop zorns-lemma-Prop
```

### Zorn's lemma for inhabited chains

```agda
module _
  (l1 l2 l3 : Level)
  where

  inhabited-zorns-lemma-Prop : Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  inhabited-zorns-lemma-Prop =
    Π-Prop
      ( Poset l1 l2)
      ( λ X →
        function-Prop
          ( is-inhabited (type-Poset X))
          ( function-Prop
            ( (C : chain-Poset l3 X) →
              is-inhabited (type-chain-Poset X C) →
              has-upper-bound-chain-Poset X C)
            ( ∃ (type-Poset X) (is-top-element-prop-Poset X))))

  inhabited-zorns-lemma : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
  inhabited-zorns-lemma = type-Prop inhabited-zorns-lemma-Prop
```

## Properties

### Zorn's lemma for inhabited chains implies Zorn's lemma

```agda
module _
  {l1 l2 l3 : Level}
  where

  zorns-lemma-inhabited-zorns-lemma :
    inhabited-zorns-lemma l1 l2 l3 → zorns-lemma l1 l2 l3
  zorns-lemma-inhabited-zorns-lemma zorn X H =
    zorn X
      ( apply-universal-property-trunc-Prop
        ( H ((λ _ → raise-empty-Prop l3) , (λ p → raise-ex-falso l3 (pr2 p))))
        ( is-inhabited-Prop (type-Poset X))
        ( λ p → unit-trunc-Prop (pr1 p)))
      ( λ C _ → H C)
```

### Assuming the law of excluded middle, Zorn's lemma implies Zorn's lemma for inhabited chains

```agda
module _
  {l1 l2 l3 : Level} (lem : LEM (l1 ⊔ l3))
  where

  inhabited-zorns-lemma-zorns-lemma :
    zorns-lemma l1 l2 l3 → inhabited-zorns-lemma l1 l2 l3
  inhabited-zorns-lemma-zorns-lemma zorn X is-inhabited-X H =
    zorn X chain-upper-bound
    where
    chain-upper-bound : (C : chain-Poset l3 X) → has-upper-bound-chain-Poset X C
    chain-upper-bound C with lem (is-inhabited-Prop (type-chain-Poset X C))
    ... | inl is-inhabited-C = H C is-inhabited-C
    ... | inr is-empty-C =
      apply-universal-property-trunc-Prop
        ( is-inhabited-X)
        ( has-upper-bound-chain-prop-Poset X C)
        ( λ x →
          intro-exists x (λ w → ex-falso (is-empty-C (unit-trunc-Prop w))))

  iff-inhabited-zorns-lemma-zorns-lemma :
    type-iff-Prop
      ( inhabited-zorns-lemma-Prop l1 l2 l3)
      ( zorns-lemma-Prop l1 l2 l3)
  iff-inhabited-zorns-lemma-zorns-lemma =
    ( zorns-lemma-inhabited-zorns-lemma , inhabited-zorns-lemma-zorns-lemma)
```

## External links

- [Zorn's lemma](https://en.wikipedia.org/wiki/Zorn%27s_lemma) at Wikipedia
- [Zorn's lemma](https://ncatlab.org/nlab/show/Zorn%27s+lemma) at $n$Lab
- [Zorn's lemma](https://mathworld.wolfram.com/ZornsLemma.html) at Wolfram
  MathWorld
