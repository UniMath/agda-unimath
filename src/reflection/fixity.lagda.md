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
data Associativity : UU lzero where
  left-associative : Associativity
  right-associative : Associativity
  non-associative : Associativity

data Precedence : UU lzero where
  related : Float → Precedence
  unrelated : Precedence

data Fixity : UU lzero where
  fixity : Associativity → Precedence → Fixity

{-# BUILTIN ASSOC Associativity #-}
{-# BUILTIN ASSOCLEFT left-associative #-}
{-# BUILTIN ASSOCRIGHT right-associative #-}
{-# BUILTIN ASSOCNON non-associative #-}

{-# BUILTIN PRECEDENCE Precedence #-}
{-# BUILTIN PRECRELATED related #-}
{-# BUILTIN PRECUNRELATED unrelated #-}

{-# BUILTIN FIXITY Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

primitive
  primQNameFixity : Name → Fixity
```

## Examples

```agda
_ : primQNameFixity (quote add-ℤ) ＝ fixity non-associative unrelated
_ = refl

_ : primQNameFixity (quote (_+ℤ_)) ＝ fixity non-associative (related 30.0)
_ = refl
```
