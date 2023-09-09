# Mixfix operators in agda-unimath

In this document, we outline our conventions for assigning precedence levels and
associativity to different
[mixfix operators in Agda](https://agda.readthedocs.io/en/v2.6.3.20230805/language/mixfix-operators.html).

## Mixfix operators in Agda

Mixfix operators in Agda can each be assigned a
[precedence level](https://agda.readthedocs.io/en/v2.6.3.20230805/language/mixfix-operators.html#precedence).
This can in principle be any signed fractional value, although we prefer them to
be non-negative integral values. The higher this value is, the higher precedence
the operator has, meaning it is evaluated before operators with lower
precedence. By default in Agda, an operator is assigned a precedence level of
`20`.

For instance, the operator `_*ℕ_` is assigned the precedence level `40`, and
`_+ℕ_` is assigned the precedence level `35`. Therefore, the expression
`x +ℕ y *ℕ z` is parsed as `x +ℕ (y *ℕ z)`.

In addition to a precedence level, every mixfix operator can be defined to be
either left or right
[associative](https://agda.readthedocs.io/en/v2.6.3.20230805/language/mixfix-operators.html#associativity).

For instance, since the pairing operator `_,_` is defined to associate to the
right, the expression `a , b , c` is parsed as `a , (b , c)`. By default, an
operator does not associate to either side.

## Operator classes

We divide the different operators into broad classes, each assigned a range of
possible precedence levels. Broadly speaking, we discern between _parametric_
and _non-parametric_ operators. The general rule is that every non-parametric
operator has higher precedence than every parametric operator. Parametric
operators are operators like the
[cartesian product](foundation-core.cartesian-product-types.md) `_×_`, the
[identity type former](foundation-core.identity-types.md) `_＝_` and the
[pairing operator](foundation.dependent-pair-types.md) `_,_`. Examples of
non-parametric operators are `_-ℤ_` `_<-ℕ_` and `_*ℤ[ω]_`.

Within these two classes, we make a further distinction between _relational_,
_additive_, _multiplicative_, _exponentiative_, and _unary_ operators, each with
a higher precedence than the previous one. All together, we assign ranges as
outlined below.

|                          | Relations | Additive | Multiplicative | Exponentiative | Unary |
| ------------------------ | --------- | -------- | -------------- | -------------- | ----- |
| Parametric Operations    | 5-9       | 10-14    | 15-19          | 20-24          | 25-29 |
| Nonparametric Operations | 30-34     | 35-39    | 40-44          | 45-49          | 50-54 |

Note that the default precedence level falls within the range of exponentiative
parametric operations.

As a rule of thumb, the lowest value in a range is assigned by default. The
notable exceptions are outlined below.

## Special rules

In this section, we outline special rules for assigning precedence levels and
associativity to particular classes of operations. Please make sure to update
this section if new rules are implemented.

### Function type-like formation operations

In Agda, the arrow notation `_→_` is directly handled by the parser, hence it
has hardcoded precedence and associativity. In particular, it has lower
precedence than any user-declared operator. To make other arrow notations
consistent with this, we consider them as relational operators and assign them
the precedence level of `5`. Other relational operators are assigned the
precedence level `6` by default.

### Reasoning syntax

Reasoning syntax is defined using Agda's mixfix operators, and should have lower
precedence than all other operators (notably except for `_→_`). The range `0-1`
is reserved for these.

### Subtractive operators

We consider the class of subtractive operators as a subclass of additive
operators. These include operators like `_-ℤ_`. Subtractive operators should
usually have higher precedence than normal additive operators, so that
expressions like `a - b + c` are parsed as `(a - b) + c`.

Moreover, subtractive operators are usually left associative, meaning that
`a - b - c` should be parsed as `(a - b) - c`.

## Table of assigned precedences

| Precedence level | Operators                                                                                                                                                                                                                                    |
| ---------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 50               | Unary non-parametric operators. This class is currently empty                                                                                                                                                                                |
| 45               | Exponentiative arithmetic operators                                                                                                                                                                                                          |
| 40               | Multiplicative arithmetic operators                                                                                                                                                                                                          |
| 36               | Subtractive arithmetic operators                                                                                                                                                                                                             |
| 35               | Additive arithmetic operators                                                                                                                                                                                                                |
| 30               | Relational arithmetic operators, `_≤-ℕ_` and `_<-ℕ_`                                                                                                                                                                                         |
| 25               | Parametric unary operators. This class is currently empty                                                                                                                                                                                    |
| 20               | Parametric exponentiative operators. This class is currently empty                                                                                                                                                                           |
| 15               | Parametric multiplicative operators like `_×_`,`_×∗_`, `_∧_`, `_∧∗_`, function composition operations like `_∘_`,`_∘∗_`, `_∘e_`, and `_∘iff_`, identification concatenation and whiskering operations like `_∙_`, `_∙h_`, `_·l_`, and `_·r_` |
| 11               | ``                                                                                                                                                                                                                                           |
| 10               | Parametric additive operators like `_+_`, `_∨_`, `_∨∗_`, list concatenation, monadic bind operations for the type checking monad                                                                                                             |
| 6                | Parametric relational operations like `_＝_`, `_~_`, `_≃_`, and `_↔_`, elementhood relations, subtype relations                                                                                                                              |
| 5                | Directed function type-like formation operations, e.g. `_→∗_` and `_↪_`                                                                                                                                                                      |
| 3                | The pairing operations `_,_` and `_,ω_`                                                                                                                                                                                                      |
| 0-1              | Reasoning syntax                                                                                                                                                                                                                             |
| -∞               | Function type formation `_→_`                                                                                                                                                                                                                |
