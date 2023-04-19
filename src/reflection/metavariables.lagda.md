# Metavariables

```agda
module reflection.metavariables where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import lists.lists
open import foundation-core.dependent-pair-types
open import foundation.cartesian-product-types
open import foundation.booleans
open import foundation.universe-levels
open import foundation.strings
open import foundation.characters
open import foundation.floats
open import foundation.machine-integers
open import foundation.unit-type
open import foundation.identity-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-integers

open import reflection.names
open import reflection.fixity
```

</details>

## Idea

-- TODO

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

