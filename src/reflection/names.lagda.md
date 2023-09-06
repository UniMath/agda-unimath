# Names

```agda
module reflection.names where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import primitives.machine-integers
open import primitives.strings
```

</details>

## Idea

The `Name` type represents quoted names, i.e. they are an abstract syntactic
representation of terms. Agda provides primitive functions to manipulate them,
giving them an equality and ordering. A closed term can be converted to a quoted
name by means of the `quote` keyword, e.g. `quote bool`.

## Definition

```agda
postulate Name : UU lzero
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name → Name → bool
  primQNameLess : Name → Name → bool
  primShowQName : Name → String
  primQNameToWord64s : Name → Word64 × Word64
  primQNameToWord64sInjective :
    ∀ a b → primQNameToWord64s a ＝ primQNameToWord64s b → a ＝ b
```

## Examples

```agda
_ : primQNameLess (quote bool) (quote unit) ＝ true
_ = refl

_ : primShowQName (quote bool) ＝ "foundation.booleans.bool"
_ = refl
```
