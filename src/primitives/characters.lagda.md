# Characters

```agda
module primitives.characters where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.universe-levels
```

</details>

## Idea

The `Char` type represents a
{{#concept "character" WD="character" WDID=Q3241972 Agda=Char}}. Agda provides
primitive functions to manipulate them. Characters are written between single
quotes, e.g. `'a'`.

## Definitions

```agda
postulate
  Char : UU lzero

{-# BUILTIN CHAR Char #-}

primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
    primIsLatin1 primIsPrint primIsHexDigit : Char → bool
  primToUpper primToLower : Char → Char
  primCharToNat : Char → ℕ
  primNatToChar : ℕ → Char
  primCharEquality : Char → Char → bool
```
