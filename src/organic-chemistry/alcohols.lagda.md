# Alcohols

```agda
open import foundation.function-extensionality-axiom

module
  organic-chemistry.alcohols
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.decidable-subtypes funext
open import foundation.dependent-pair-types
open import foundation.negation funext
open import foundation.propositional-truncations funext
open import foundation.universe-levels
open import foundation.unordered-pairs funext

open import organic-chemistry.hydrocarbons funext
open import organic-chemistry.saturated-carbons funext
```

</details>

## Idea

An alcohol is a hydrocarbon with at least one `-OH` group. The type of alcohols
can therefore be defined as the type of hydrocarbons equipped with a
distinguished subset of the available (unbonded) electrons of the carbon atoms.

## Definition

```agda
alcohol : UU (lsuc lzero)
alcohol =
  Σ ( hydrocarbon lzero lzero)
    ( λ X →
      Σ ( (c : vertex-hydrocarbon X) →
          decidable-subtype lzero (electron-carbon-atom-hydrocarbon X c))
        ( λ OH →
          ( ( c c' : vertex-hydrocarbon X) →
            ( b : edge-hydrocarbon X (standard-unordered-pair c c')) →
            ¬ (is-in-decidable-subtype (OH c) (bonding-hydrocarbon X b))) ×
          ( ( type-trunc-Prop
            ( Σ ( vertex-hydrocarbon X)
                ( λ c → type-decidable-subtype (OH c)))) ×
            ( ( c : vertex-hydrocarbon X) →
              type-decidable-subtype (OH c) →
              is-saturated-carbon-hydrocarbon X c
              ))))
```

More explicitly, an alcohol is a hydrocarbon equipped with, for each of its
carbons, a subset of its electrons, where membership in that subset indicates
whether or not a hydroxyl group is bonded to that specific electron. We require
the following conditions:

- The electron shared between a carbon atom and a hydroxyl group can not also be
  shared between that carbon atom and a different carbon.
- There must be at least one hydroxyl group.
- Atoms to which hydroxyl groups are bonded must be saturated.
