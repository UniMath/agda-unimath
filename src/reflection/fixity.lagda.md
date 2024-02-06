# Fixity

```agda
module reflection.fixity where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers

open import foundation.identity-types
open import foundation.universe-levels

open import primitives.floats

open import reflection.names
```

</details>

## Idea

The fixity of a quoted name is given by

- An associativity, i.e. it is left-associative, right-associative or neither.
- A precedence, i.e. it is unrelated (it has no precedence) or it is related and
  has a float precedence.

## Definition

```agda
data Associativity-Agda : UU lzero where
  left-associative : Associativity-Agda
  right-associative : Associativity-Agda
  nonassociative : Associativity-Agda

data Precedence-Agda : UU lzero where
  related : Float → Precedence-Agda
  unrelated : Precedence-Agda

data Fixity-Agda : UU lzero where
  fixity : Associativity-Agda → Precedence-Agda → Fixity-Agda

{-# BUILTIN ASSOC Associativity-Agda #-}
{-# BUILTIN ASSOCLEFT left-associative #-}
{-# BUILTIN ASSOCRIGHT right-associative #-}
{-# BUILTIN ASSOCNON nonassociative #-}

{-# BUILTIN PRECEDENCE Precedence-Agda #-}
{-# BUILTIN PRECRELATED related #-}
{-# BUILTIN PRECUNRELATED unrelated #-}

{-# BUILTIN FIXITY Fixity-Agda #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

primitive
  primQNameFixity : Name-Agda → Fixity-Agda
```

## Examples

```agda
_ : primQNameFixity (quote add-ℤ) ＝ fixity nonassociative unrelated
_ = refl

_ : primQNameFixity (quote (_+ℤ_)) ＝ fixity left-associative (related 35.0)
_ = refl
```
