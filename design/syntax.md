# Syntax

```
<knd> ::=
  | Type → <knd>
  | Type

<typ1> ::=
  | ∀ (<typ> <: <typ-var> <: <typ>) ↦ <typ1>
  | <typ>

<typ> ::=
  | <typ-var>
  | <tag>#<typ>
  | <typ>.<tag>
  | Void 
  | Unit
  | <typ> & <typ>
  | <typ> | <typ> 
  | μ (<typ-var> : <knd>) ↦ <typ>
  | <typ-var> <typ>

<trm> ::=
  | <trm-var>
  | <tag>#<trm>
  | <trm>.<tag>
  | unit
  | <trm> , <trm>
  | λ (<trm-var> : <typ>) ↦ <trm>
  | <trm> <trm>
  | Λ (<typ> <: <typ-var> <: <typ>) ↦ <trm>
  | <trm> <typ>
  | μ (<trm-var> : <typ1>) ↦ <trm>
  | let <trm-var> : <typ1> = <trm> in <trm>
  | let <typ-var> : <knd> = <typ> in <trm>

<tag> ::= <tag-name>
<typ-var> ::= <type-variable-name>
<trm-var> ::= <term-variable-name>
```