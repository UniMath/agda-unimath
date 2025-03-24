# The universal property of the conatural numbers

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.universal-property-conatural-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.coalgebras-maybe funext univalence
open import foundation.contractible-types funext univalence
open import foundation.dependent-products-contractible-types funext
open import foundation.morphisms-coalgebras-maybe funext univalence
open import foundation.universe-levels
```

</details>

## Idea

The [conatural numbers](elementary-number-theory.conatural-numbers.md) `ℕ∞`
enjoys many universal properties, among others:

1. It is the one-point compactification of the
   [natural numbers](elementary-number-theory.natural-numbers.md).
2. It classifies downward-stable subsets of the natural numbers.
3. It is the final coalgebra of the [maybe monad](foundation-core.maybe.md).

On this page we consider the last of these. Thus, a
`Maybe`-[coalgebra](foundation.coalgebras-maybe.md) `η : X → Maybe X` satisfies
the
{{#concept "universal property of the conatural numbers" Agda=universal-property-conatural-numbers}}
if, for every other `Maybe`-coalgebra `η' : Y → Maybe Y` there is a
[unique](foundation-core.contractible-types.md)
[coalgebra homomorphism](foundation.morphisms-coalgebras-maybe.md)

```text
            f
     Y ----------> X
     |             |
   η'|             | η
     ∨             ∨
  Maybe Y ----> Maybe X.
         Maybe f
```

## Definitions

### The universal property of the conatural numbers at a universe level

```agda
universal-property-conatural-numbers-Level :
  {l1 : Level} → coalgebra-Maybe l1 → (l : Level) → UU (l1 ⊔ lsuc l)
universal-property-conatural-numbers-Level N∞ l =
  (X : coalgebra-Maybe l) → is-contr (hom-coalgebra-Maybe X N∞)
```

### The universal property of the conatural numbers at a universe level

```agda
universal-property-conatural-numbers :
  {l1 : Level} → coalgebra-Maybe l1 → UUω
universal-property-conatural-numbers N∞ =
  {l : Level} → universal-property-conatural-numbers-Level N∞ l
```
