# Fixity

```agda
open import foundation.function-extensionality-axiom

module
  reflection.fixity
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers funext

open import foundation.universe-levels

open import foundation-core.identity-types

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
  left-Associativity-Agda : Associativity-Agda
  right-Associativity-Agda : Associativity-Agda
  none-Associativity-Agda : Associativity-Agda

data Precedence-Agda : UU lzero where
  related-Precedence-Agda : Float → Precedence-Agda
  unrelated-Precedence-Agda : Precedence-Agda

data Fixity-Agda : UU lzero where
  cons-Fixity-Agda : Associativity-Agda → Precedence-Agda → Fixity-Agda

{-# BUILTIN ASSOC Associativity-Agda #-}
{-# BUILTIN ASSOCLEFT left-Associativity-Agda #-}
{-# BUILTIN ASSOCRIGHT right-Associativity-Agda #-}
{-# BUILTIN ASSOCNON none-Associativity-Agda #-}

{-# BUILTIN PRECEDENCE Precedence-Agda #-}
{-# BUILTIN PRECRELATED related-Precedence-Agda #-}
{-# BUILTIN PRECUNRELATED unrelated-Precedence-Agda #-}

{-# BUILTIN FIXITY Fixity-Agda #-}
{-# BUILTIN FIXITYFIXITY cons-Fixity-Agda #-}

primitive
  primQNameFixity : Name-Agda → Fixity-Agda
```

## Examples

```agda
_ :
  primQNameFixity (quote add-ℤ) ＝
  cons-Fixity-Agda none-Associativity-Agda unrelated-Precedence-Agda
_ = refl

_ :
  primQNameFixity (quote (_+ℤ_)) ＝
  cons-Fixity-Agda left-Associativity-Agda (related-Precedence-Agda 35.0)
_ = refl
```
