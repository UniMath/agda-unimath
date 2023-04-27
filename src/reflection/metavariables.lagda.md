# Metavariables

```agda
module reflection.metavariables where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.dependent-pair-types

open import lists.lists

open import primitive-types.characters
open import primitive-types.floats
open import primitive-types.machine-integers
open import primitive-types.strings

open import reflection.fixity
open import reflection.names
```

</details>

## Idea

The `Meta` type represents metavariables in Agda.

## Definition

```agda
postulate Meta : UU lzero
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → bool
  primMetaLess     : Meta → Meta → bool
  primShowMeta     : Meta → String
  primMetaToNat    : Meta → ℕ
  primMetaToNatInjective : ∀ a b → primMetaToNat a ＝ primMetaToNat b → a ＝ b
```
