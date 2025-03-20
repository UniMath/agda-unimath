# Names

```agda
module reflection.names where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.booleans
open import foundation-core.identity-types

open import primitives.machine-integers
open import primitives.strings
```

</details>

## Idea

The `Name-Agda` type represents quoted names, i.e. they are an abstract
syntactic representation of terms. Agda provides primitive functions to
manipulate them, giving them an equality and ordering. A closed term can be
converted to a quoted name by means of the `quote` keyword, e.g. `quote bool`.

## Definition

```agda
postulate
  Name-Agda : UU lzero

{-# BUILTIN QNAME Name-Agda #-}

primitive
  primQNameEquality : Name-Agda → Name-Agda → bool
  primQNameLess : Name-Agda → Name-Agda → bool
  primShowQName : Name-Agda → String
  primQNameToWord64s : Name-Agda → Word64 × Word64
  primQNameToWord64sInjective :
    (a b : Name-Agda) → primQNameToWord64s a ＝ primQNameToWord64s b → a ＝ b
```

## Examples

```text
_ : primQNameLess (quote bool) (quote unit) ＝ true
_ = refl

_ : primShowQName (quote bool) ＝ "foundation-core.booleans.bool"
_ = refl
```
