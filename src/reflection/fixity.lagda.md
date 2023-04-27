# Fixity

```agda
module reflection.fixity where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers

open import foundation.identity-types
open import foundation.universe-levels

open import primitive-types.floats

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
  left-assoc  : Associativity
  right-assoc : Associativity
  non-assoc   : Associativity

data Precedence : UU lzero where
  related   : Float → Precedence
  unrelated : Precedence

data Fixity : UU lzero where
  fixity : Associativity → Precedence → Fixity

{-# BUILTIN ASSOC      Associativity #-}
{-# BUILTIN ASSOCLEFT  left-assoc    #-}
{-# BUILTIN ASSOCRIGHT right-assoc   #-}
{-# BUILTIN ASSOCNON   non-assoc     #-}

{-# BUILTIN PRECEDENCE    Precedence #-}
{-# BUILTIN PRECRELATED   related    #-}
{-# BUILTIN PRECUNRELATED unrelated  #-}

{-# BUILTIN FIXITY       Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

primitive
  primQNameFixity : Name → Fixity
```

## Examples

```agda
_ : primQNameFixity (quote add-ℤ) ＝ fixity non-assoc unrelated
_ = refl

_ : primQNameFixity (quote (_+ℤ_)) ＝ fixity non-assoc (related 30.0)
_ = refl
```
