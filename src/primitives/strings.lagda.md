# Strings

```agda
module primitives.strings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.booleans
open import foundation-core.maybe

open import lists.lists

open import primitives.characters
```

</details>

## Idea

The `String` type represents strings. Agda provides primitive functions to
manipulate them. Strings are written between double quotes, e.g.
`"agda-unimath"`.

## Definitions

```agda
postulate
  String : UU lzero

{-# BUILTIN STRING String #-}

primitive
  primStringUncons : String → Maybe' (Σ Char (λ _ → String))
  primStringToList : String → list Char
  primStringFromList : list Char → String
  primStringAppend : String → String → String
  primStringEquality : String → String → bool
  primShowChar : Char → String
  primShowString : String → String
  primShowNat : ℕ → String
```
