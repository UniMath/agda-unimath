# Floats

```agda
module primitives.floats where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.maybe
open import foundation.universe-levels

open import primitives.machine-integers
open import primitives.strings
```

</details>

## Idea

The `Float` type represents {{#concept "IEEE754 floats" Agda=Float}}. Agda
provides primitive functions to manipulate them. Floats can be written as in
usual programming languages, using dots as separators, e.g. `3.14`.

## Definitions

```agda
postulate
  Float : UU lzero

{-# BUILTIN FLOAT Float #-}

primitive
  -- Relations
  primFloatInequality : Float → Float → bool
  primFloatEquality : Float → Float → bool
  primFloatLess : Float → Float → bool
  primFloatIsInfinite : Float → bool
  primFloatIsNaN : Float → bool
  primFloatIsNegativeZero : Float → bool
  primFloatIsSafeInteger : Float → bool
  -- Conversions
  primFloatToWord64 : Float → Maybe' Word64
  primNatToFloat : ℕ → Float
  -- primIntToFloat             : Int → Float
  -- primFloatRound             : Float → Maybe' Int
  -- primFloatFloor             : Float → Maybe' Int
  -- primFloatCeiling           : Float → Maybe' Int
  -- primFloatToRatio           : Float → (Σ Int λ _ → Int)
  -- primRatioToFloat           : Int → Int → Float
  -- primFloatDecode            : Float → Maybe' (Σ Int λ _ → Int)
  -- primFloatEncode            : Int → Int → Maybe' Float
  primShowFloat : Float → String
  -- Operations
  primFloatPlus : Float → Float → Float
  primFloatMinus : Float → Float → Float
  primFloatTimes : Float → Float → Float
  primFloatDiv : Float → Float → Float
  primFloatPow : Float → Float → Float
  primFloatNegate : Float → Float
  primFloatSqrt : Float → Float
  primFloatExp : Float → Float
  primFloatLog : Float → Float
  primFloatSin : Float → Float
  primFloatCos : Float → Float
  primFloatTan : Float → Float
  primFloatASin : Float → Float
  primFloatACos : Float → Float
  primFloatATan : Float → Float
  primFloatATan2 : Float → Float → Float
  primFloatSinh : Float → Float
  primFloatCosh : Float → Float
  primFloatTanh : Float → Float
  primFloatASinh : Float → Float
  primFloatACosh : Float → Float
  primFloatATanh : Float → Float
```
